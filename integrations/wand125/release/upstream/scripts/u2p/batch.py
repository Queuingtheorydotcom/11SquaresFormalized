"""Run the generator on many cases in parallel; write OUTDIR/C<i>/ and a summary JSON line per case.
Usage: python3 batch.py JOBS OUTDIR CASE [CASE ...]   (env U2P_PREFIX: module prefix, default U2P)"""
import json
import multiprocessing as mp
import os
import sys
import time
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def one(args):
    ci, outdir = args
    prefix = os.environ.get('U2P_PREFIX', 'U2P')
    import gen_u2p as G
    G.KMAX = 16
    t0 = time.time()
    logf = open(os.path.join(outdir, f"C{ci}.log"), "w")
    try:
        J, steps = G.exclude(ci, log=lambda s: (logf.write(s + "\n"), logf.flush()))
        kmax = G.KMAX
        if steps is None and G.KMAX:
            logf.write("retry without a target limit\n")
            G.KMAX = 0
            J, steps = G.exclude(ci, log=lambda s: (logf.write(s + "\n"), logf.flush()))
            kmax = 0
        if steps is None:
            return {"case": ci, "status": "FAILED", "seconds": round(time.time() - t0)}
        k, tot = G.emit_case(ci, J, steps, outdir, prefix)
        return {"case": ci, "status": "OK", "kmax": kmax, "steps_searched": len(steps), "steps_kept": k,
                "leaves": tot, "seconds": round(time.time() - t0)}
    except Exception:
        logf.write(traceback.format_exc())
        return {"case": ci, "status": "ERROR", "seconds": round(time.time() - t0)}
    finally:
        logf.close()


if __name__ == "__main__":
    jobs, outdir = int(sys.argv[1]), sys.argv[2]
    cases = [int(c) for c in sys.argv[3:]]
    os.makedirs(outdir, exist_ok=True)
    with mp.Pool(jobs) as pool, open(os.path.join(outdir, "summary.jsonl"), "a") as out:
        for r in pool.imap_unordered(one, [(c, outdir) for c in cases]):
            out.write(json.dumps(r) + "\n")
            out.flush()
            print(json.dumps(r), flush=True)
