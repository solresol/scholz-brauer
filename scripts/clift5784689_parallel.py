#!/usr/bin/env python3
"""Checkpointed parallel driver for clift5784689_loss_search.

The search of one anchor is split at a depth into independent jobs (search
states). Workers run batches of jobs with a time limit; the jobs of a batch
that exceeds it are rerun alone, and a job that alone exceeds it is split
again `step` levels deeper and its sub-jobs are queued (results are exact: a
split run counts the nodes above the new jobs, each job counts its own subtree).
Every finished record is appended to <workdir>/records.jsonl, so an interrupted
run resumes where it stopped.

    uv run scripts/clift5784689_parallel.py BINARY A B C ANCHOR WORKDIR \
        [--workers 3] [--depth 10] [--step 3] [--timeout 120] [--batch 32] [--var XYZ] [--s S] [--halve-all]

The binary's extra options are kept in <workdir>/options.json.
"""
import argparse
import json
from pathlib import Path
import queue
import subprocess
import threading
import time


def job_depth(line):
    f = line.split()
    return sum(1 for x in f[1:7] if int(x) >= 0) + int(f[7])


def run_search(binary, a, b, c, anchor, workdir, workers=3, depth=10, step=3, timeout=120, log=print,
               batch_size=32, extra=()):
    workdir = Path(workdir)
    workdir.mkdir(parents=True, exist_ok=True)
    abc = [str(a), str(b), str(c)]
    extra = list(extra)
    opt_path = workdir / 'options.json'  # the search options, for the evidence reports
    if opt_path.exists():
        if json.loads(opt_path.read_text())['extra'] != extra:
            raise SystemExit('workdir was searched with other options')
    else:
        opt_path.write_text(json.dumps({'extra': extra}) + '\n')
    records_path = workdir / 'records.jsonl'
    records = {}
    if records_path.exists():
        for line in records_path.read_text().splitlines():
            r = json.loads(line)
            records[r['id']] = r
    root_jobs = workdir / 'root.jobs'
    if 'root' not in records:
        out = workdir / 'root.out'
        for p in (out, root_jobs):
            if p.exists():
                p.unlink()
        res = subprocess.run([binary] + abc + [anchor, str(out), 'split=%d' % depth] + extra,
                             capture_output=True, text=True, check=True)
        stats = json.loads(res.stdout)
        lines = out.read_text().splitlines()
        jobs = [l for l in lines if l.startswith('J')]
        root_jobs.write_text(''.join(l + '\n' for l in jobs))
        rec = {'id': 'root', 'kind': 'split', 'nodes': stats['nodes'], 'jobs': stats['jobs'],
               'configurations': [l for l in lines if l.startswith('C')], 'children': len(jobs)}
        records['root'] = rec
        with records_path.open('a') as fh:
            fh.write(json.dumps(rec) + '\n')
    # rebuild the pending job tree from the split records
    pending = queue.Queue()
    jobfile = {'root': root_jobs}

    def children(rid):
        return jobfile[rid].read_text().splitlines()

    stack = ['root']
    while stack:
        rid = stack.pop()
        for k, line in enumerate(children(rid)):
            cid = '%s.%d' % (rid, k)
            if cid in records:
                if records[cid]['kind'] == 'split':
                    jobfile[cid] = workdir / ('%s.jobs' % cid)
                    stack.append(cid)
            else:
                pending.put((cid, line))
    lock = threading.Lock()
    fh = records_path.open('a')
    t0 = time.time()
    active = [0]

    def save(rec):
        with lock:
            records[rec['id']] = rec
            fh.write(json.dumps(rec) + '\n')
            fh.flush()

    solo = queue.Queue()  # jobs that timed out inside a batch: rerun alone

    def run_alone(cid, line):
        out = workdir / ('%s.out' % cid)
        if out.exists():
            out.unlink()
        begin = time.time()
        try:
            res = subprocess.run([binary] + abc + ['resume', str(out)] + extra, input=line + '\n',
                                 capture_output=True, text=True, timeout=timeout, check=True)
            job = json.loads(res.stdout.splitlines()[0])
            cfg = [l for l in out.read_text().splitlines() if l.startswith('C')]
            out.unlink()
            save({'id': cid, 'kind': 'run', 'nodes': job['nodes'], 'configurations': cfg,
                  'seconds': round(time.time() - begin, 3)})
        except subprocess.TimeoutExpired:
            if out.exists():
                out.unlink()
            d = job_depth(line) + step
            res = subprocess.run([binary] + abc + ['resume', str(out), 'split=%d' % d] + extra,
                                 input=line + '\n', capture_output=True, text=True, check=True)
            job = json.loads(res.stdout.splitlines()[0])
            lines = out.read_text().splitlines()
            jobs = [l for l in lines if l.startswith('J')]
            jf = workdir / ('%s.jobs' % cid)
            jf.write_text(''.join(l + '\n' for l in jobs))
            out.unlink()
            with lock:
                jobfile[cid] = jf
            save({'id': cid, 'kind': 'split', 'nodes': job['nodes'], 'jobs': job['jobs'],
                  'configurations': [l for l in lines if l.startswith('C')],
                  'children': len(jobs), 'depth': d, 'timeout': timeout})
            for k, sub in enumerate(jobs):
                pending.put(('%s.%d' % (cid, k), sub))

    def run_batch(batch):
        """Several jobs in one process (one JSON line each, in order)."""
        out = workdir / ('%s.batch.out' % batch[0][0])
        if out.exists():
            out.unlink()
        begin = time.time()
        try:
            res = subprocess.run([binary] + abc + ['resume', str(out)] + extra,
                                 input=''.join(line + '\n' for _, line in batch),
                                 capture_output=True, text=True, timeout=timeout, check=True)
        except subprocess.TimeoutExpired:
            if out.exists():
                out.unlink()
            for item in batch:
                solo.put(item)
            return
        cfg = [l for l in out.read_text().splitlines() if l.startswith('C')]
        out.unlink()
        lines = [json.loads(l) for l in res.stdout.splitlines() if l.startswith('{"job"')]
        if len(lines) != len(batch):
            raise ValueError('batch output length')
        if cfg:  # attribute configurations exactly by rerunning each job alone
            for item in batch:
                run_alone(*item)
            return
        sec = round((time.time() - begin) / len(batch), 3)
        for (cid, _), job in zip(batch, lines):
            save({'id': cid, 'kind': 'run', 'nodes': job['nodes'], 'configurations': [],
                  'seconds': sec, 'batched': len(batch)})

    def worker():
        while True:
            try:
                item = solo.get_nowait()
                with lock:
                    active[0] += 1
                try:
                    run_alone(*item)
                finally:
                    with lock:
                        active[0] -= 1
                continue
            except queue.Empty:
                pass
            batch = []
            try:
                batch.append(pending.get(timeout=1))
                while len(batch) < batch_size:
                    batch.append(pending.get_nowait())
            except queue.Empty:
                pass
            if not batch:
                with lock:
                    if active[0] == 0 and pending.empty() and solo.empty():
                        return
                continue
            with lock:
                active[0] += 1
            try:
                if len(batch) == 1:
                    run_alone(*batch[0])
                else:
                    run_batch(batch)
            finally:
                with lock:
                    active[0] -= 1

    threads = [threading.Thread(target=worker) for _ in range(workers)]
    for t in threads:
        t.start()
    last = time.time()
    while any(t.is_alive() for t in threads):
        time.sleep(2)
        if time.time() - last > 600:
            with lock:
                log('progress records %d pending %d elapsed %ds' % (len(records), pending.qsize(), time.time() - t0))
            last = time.time()
    for t in threads:
        t.join()
    fh.close()
    return summarise(records, workdir)


def summarise(records, workdir):
    """Exact totals over the job tree; fails unless every job has a record."""
    jobs_of = {}
    for rid, r in records.items():
        if r['kind'] == 'split':
            jobs_of[rid] = (Path(workdir) / ('%s.jobs' % rid)).read_text().splitlines() \
                if rid != 'root' else (Path(workdir) / 'root.jobs').read_text().splitlines()
            if len(jobs_of[rid]) != r['children'] or r['children'] != r['jobs']:
                raise ValueError('split record %s inconsistent' % rid)
    nodes, configs, runs, splits, longest = 0, [], 0, 0, 0.0
    stack = ['root']
    while stack:
        rid = stack.pop()
        r = records.get(rid)
        if r is None:
            raise ValueError('job %s has no record' % rid)
        configs += r['configurations']
        if r['kind'] == 'split':
            splits += 1
            nodes += r['nodes'] - r['jobs']
            stack.extend('%s.%d' % (rid, k) for k in range(r['children']))
        else:
            runs += 1
            nodes += r['nodes']
            longest = max(longest, r['seconds'])
    return {'nodes': nodes, 'configurations': configs, 'job_runs': runs, 'splits': splits,
            'longest_job_seconds': longest}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('binary')
    ap.add_argument('a', type=int)
    ap.add_argument('b', type=int)
    ap.add_argument('c', type=int)
    ap.add_argument('anchor', choices=['t', 'A1'])
    ap.add_argument('workdir')
    ap.add_argument('--workers', type=int, default=3)
    ap.add_argument('--depth', type=int, default=10)
    ap.add_argument('--step', type=int, default=3)
    ap.add_argument('--timeout', type=float, default=120)
    ap.add_argument('--batch', type=int, default=32)
    ap.add_argument('--var', default='000', help='chord variant XYZ (chains 9-16 and 1-8)')
    ap.add_argument('--s', type=int, default=1, help='doublings from "2" to "4" (10 for chains 1-8)')
    ap.add_argument('--halve-all', action='store_true', help='halving test for every class (option halve=all)')
    args = ap.parse_args()
    t0 = time.time()
    s = run_search(args.binary, args.a, args.b, args.c, args.anchor, args.workdir, args.workers,
                   args.depth, args.step, args.timeout, log=lambda m: print(m, flush=True),
                   batch_size=args.batch,
                   extra=(['var=' + args.var] if args.var != '000' else []) + (['s=%d' % args.s] if args.s != 1 else [])
                   + (['halve=all'] if args.halve_all else []))
    s['wall_seconds'] = round(time.time() - t0, 1)
    print(json.dumps(s), flush=True)


if __name__ == '__main__':
    main()
