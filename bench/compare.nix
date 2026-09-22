# serde_json vs ezjson compare script text (embedded; not a checked-in .py file).
# Consumed by writeText / writeShellApplication in default.nix.
#
# Fairness / what the numbers mean:
# - Encode/decode speed: ezjson parse/print (native ELF, IO.now) vs a Rust
#   serde_json binary that loops N times in-process. Disk open is outside both
#   timers; never spawn rustc or a new process per op as a “reference.”
# - Ratio = ezjson/rust (>1 ⇒ ezjson slower). Absolute ms/op for both.
# - Fixtures are product-shaped: nested objects/arrays, unicode, numbers,
#   mixed sizes ~1KB–100KB+. Tiny edge cases stay in correctness only.
# - IO.now / Instant are 1 ms. If MS is 0, N is raised; if still unresolved,
#   wall/n is reported honestly without claiming a vs-rust win.
{ drvBin ? "ezjson-bench", rustBin ? "ezjson-rust-ref" }:
''
import json, os, random, string, subprocess, sys, time, traceback

DRV = os.environ.get("EZJSON_BENCH_DRV", "${drvBin}")
RUST = os.environ.get("EZJSON_BENCH_RUST", "${rustBin}")
WORK = os.environ.get("EZJSON_BENCH_WORK", os.path.join(os.environ.get("TMPDIR", "/tmp"), "ezjson-bench-work"))
MODE = os.environ.get("EZJSON_BENCH_MODE", "correctness")  # correctness | speed | all
os.makedirs(WORK, exist_ok=True)

lines, cases, speed_rows = [], [], []
fails = 0

def log(msg=""):
    print(msg, flush=True)
    lines.append(msg)

def run_bin(bin_path, args, timeout):
    t0 = time.perf_counter()
    try:
        r = subprocess.run([bin_path, *args], capture_output=True, timeout=timeout)
        return {"rc": r.returncode, "out": r.stdout.decode("utf-8", "replace"),
                "err": r.stderr.decode("utf-8", "replace"), "wall": time.perf_counter() - t0,
                "timeout": False}
    except subprocess.TimeoutExpired as e:
        out = e.stdout or b""; err = e.stderr or b""
        if isinstance(out, str): out = out.encode()
        if isinstance(err, str): err = err.encode()
        return {"rc": None, "out": out.decode("utf-8", "replace"),
                "err": err.decode("utf-8", "replace"),
                "wall": time.perf_counter() - t0, "timeout": True}

def ez(args, timeout=60):
    return run_bin(DRV, args, timeout)

def rust(args, timeout=60):
    return run_bin(RUST, args, timeout)

def parse_bench(out):
    parts = out.split()
    if len(parts) < 8 or parts[0] != "MS":
        return None
    return {parts[i]: int(parts[i + 1]) for i in range(0, len(parts) - 1, 2)}

def add_case(group, name, status, detail, hard=True):
    global fails
    cases.append({"group": group, "name": name, "status": status, "detail": detail, "hard": hard})
    log(f"[{status}] {group} | {name}")
    log(f"    {detail}")
    if hard and status != "PASS":
        fails += 1

def write_fixture(name, text):
    path = os.path.join(WORK, name)
    open(path, "w", encoding="utf-8").write(text)
    return path

def semantic_eq(a_text, b_text):
    # Compare as JSON values (number spelling / key order may differ in print).
    try:
        return json.loads(a_text) == json.loads(b_text)
    except Exception:
        return False

def load_out(path):
    return open(path, "r", encoding="utf-8").read()

# --- Fixtures ---

def edge_fixtures():
    # Correctness control cases (including rejects). Not used for speed.
    return [
        ("null", "null", True),
        ("bools", "[true,false]", True),
        ("empty_obj", "{}", True),
        ("empty_arr", "[]", True),
        ("nums", "[0,-12,3.50,1e9]", True),
        ("space", ' { "a" : [ 1 , 2 ] ,\\n\\t"b" : { } } ', True),
        ("nest", '[[[]],{"k":{"k":[null]}}]', True),
        ("unicode", '{"msg":"你好🌍","esc":"A\\u0041"}', True),
        ("mixed", '{"id":7,"ok":true,"tags":[null,"x"],"n":-2.5e3}', True),
        ("reject_empty", "", False),
        ("reject_two_roots", "1 2", False),
        ("reject_trailing", "[1,2,]", False),
        ("reject_unclosed", '{"a":1', False),
    ]

def real_world_fixtures():
    # Product-shaped docs: nested objects/arrays, unicode, numbers; ~1KB–100KB+.
    rng = random.Random(42)

    def obj_row(i):
        return {
            "id": i,
            "sku": f"SKU-{i:05d}",
            "name": f"品目-{i}-αβγ",
            "price": round(rng.uniform(1.0, 999.99), 2),
            "qty": rng.randint(0, 500),
            "tags": [f"t{j}" for j in range(1 + (i % 4))],
            "meta": {
                "active": bool(i % 2),
                "score": rng.random(),
                "note": "naïve café — 東京" if i % 3 == 0 else "plain",
            },
        }

    def dumps(data):
        return json.dumps(data, ensure_ascii=False, separators=(",", ":"))

    def grow(name, data, want, append_row):
        text = dumps(data)
        while len(text.encode("utf-8")) < want:
            append_row(data)
            text = dumps(data)
        return (name, text, len(text.encode("utf-8")))

    small = {
        "api": "v1",
        "user": {"id": 42, "name": "Ada Łukasiewicz", "roles": ["admin", "ops"]},
        "prefs": {"theme": "dark", "locale": "ja-JP", "flags": {"beta": True}},
        "nums": [0, -1, 3.14159, 1e-6, 1e9],
        "tree": {"a": {"b": {"c": [1, 2, {"d": "深度"}]}}},
        "pad": "",
    }
    medium = {
        "catalog": [obj_row(i) for i in range(40)],
        "summary": {"count": 40, "currency": "USD", "note": "中サイズ fixture"},
    }
    large = {
        "batch": [obj_row(i) for i in range(200)],
        "index": {f"k{i}": i * i for i in range(100)},
        "blob": "".join(rng.choice(string.ascii_letters + "αβγδεζη東京") for _ in range(2000)),
        "nested": {"layers": [{"n": n, "kids": [{"m": m} for m in range(5)]} for n in range(20)]},
    }
    return [
        grow("cfg_1kb", small, 1000, lambda d: d.__setitem__("pad", d.get("pad", "") + ("あ" * 40))),
        grow("catalog_10kb", medium, 10000, lambda d: d["catalog"].append(obj_row(len(d["catalog"])))),
        grow("batch_100kb", large, 100000, lambda d: d["batch"].append(obj_row(len(d["batch"])))),
    ]

def correct_edges():
    log("\\n== Edge / RFC-shaped correctness ==")
    for name, text, ok in edge_fixtures():
        src = write_fixture("edge_" + name + ".json", text)
        ez_dst = src + ".ez.out"
        rs_dst = src + ".rs.out"
        er = ez(["json-dec", src, ez_dst], 30)
        rr = rust(["json-dec", src, rs_dst], 30)
        if not ok:
            ez_fail = er["timeout"] or er["rc"] != 0 or not os.path.exists(ez_dst)
            rs_fail = rr["timeout"] or rr["rc"] != 0 or not os.path.exists(rs_dst)
            # Accept reject if ezjson fails; rust may also fail — both failing is PASS.
            status = "PASS" if ez_fail else "FAIL"
            add_case("A reject", name, status,
                     f"ezjson rc={er['rc']} rust rc={rr['rc']} (expect ezjson reject)")
            continue
        if er["timeout"] or er["rc"] != 0 or not os.path.exists(ez_dst):
            add_case("B ezjson decode", name, "FAIL", f"rc={er['rc']} err={er['err'][:160]}")
            continue
        if rr["timeout"] or rr["rc"] != 0 or not os.path.exists(rs_dst):
            add_case("B rust decode", name, "FAIL", f"rc={rr['rc']} err={rr['err'][:160]}")
            continue
        ez_out = load_out(ez_dst)
        rs_out = load_out(rs_dst)
        ok_sem = semantic_eq(ez_out, rs_out)
        add_case("B cross-decode semantic", name, "PASS" if ok_sem else "FAIL",
                 f"ezjson {len(ez_out)}B rust {len(rs_out)}B eq={ok_sem}")
        # ezjson round-trip stability (print is compact; semantic vs rust)
        rt_dst = src + ".ez.rt"
        tr = ez(["json-rt", src, rt_dst], 30)
        if tr["timeout"] or tr["rc"] != 0 or not os.path.exists(rt_dst):
            add_case("C ezjson round-trip", name, "FAIL", f"rc={tr['rc']}")
        else:
            rt = load_out(rt_dst)
            ok_rt = semantic_eq(rt, rs_out) and semantic_eq(rt, ez_out)
            add_case("C ezjson round-trip", name, "PASS" if ok_rt else "FAIL",
                     f"rt {len(rt)}B")

def correct_real():
    log("\\n== Real-world fixture correctness ==")
    for name, text, nbytes in real_world_fixtures():
        src = write_fixture("real_" + name + ".json", text)
        ez_dst = src + ".ez.out"
        rs_dst = src + ".rs.out"
        er = ez(["json-dec", src, ez_dst], 120)
        rr = rust(["json-dec", src, rs_dst], 120)
        if er["timeout"] or er["rc"] != 0 or not os.path.exists(ez_dst):
            add_case("D real ezjson", name, "FAIL", f"rc={er['rc']} size={nbytes}")
            continue
        if rr["timeout"] or rr["rc"] != 0 or not os.path.exists(rs_dst):
            add_case("D real rust", name, "FAIL", f"rc={rr['rc']} size={nbytes}")
            continue
        ez_out = load_out(ez_dst)
        rs_out = load_out(rs_dst)
        ok_sem = semantic_eq(ez_out, rs_out)
        add_case("D real cross-decode", name, "PASS" if ok_sem else "FAIL",
                 f"{nbytes}B in; ez={len(ez_out)} rs={len(rs_out)}")
        # Encode path: both print compact from the same input text
        ez_enc = src + ".ez.enc"
        rs_enc = src + ".rs.enc"
        ee = ez(["json-enc", src, ez_enc], 120)
        re = rust(["json-enc", src, rs_enc], 120)
        if ee["rc"] != 0 or re["rc"] != 0:
            add_case("E real encode", name, "FAIL", f"ez={ee['rc']} rust={re['rc']}")
        else:
            ok_e = semantic_eq(load_out(ez_enc), load_out(rs_enc))
            add_case("E real encode semantic", name, "PASS" if ok_e else "FAIL",
                     f"encode eq={ok_e}")

def ms_per(parsed, wall, n):
    if parsed is None:
        return None, "no-parse"
    if parsed["MS"] > 0:
        return parsed["MS"] / float(n), "timer"
    return (wall * 1000.0 / float(n)), "MS=0; wall/n"

def run_bench_bump(bin_path, args_prefix, n0, timeout, max_n=65536):
    # Raise N until MS>0 or max_n.
    n = n0
    last = None
    while True:
        r = run_bin(bin_path, [*args_prefix, str(n)], timeout)
        last = (r, parse_bench(r["out"]) if not r["timeout"] else None, n)
        if r["timeout"]:
            return last
        parsed = last[1]
        if parsed is None:
            return last
        if parsed["MS"] > 0 or n >= max_n:
            return last
        n = min(max_n, max(n * 4, n + 1))

def speed():
    log("\\n== Speed (printable; does not fail the check) ==")
    log("FAIR: in-memory ezjson parse/print vs in-process serde_json (N loops inside one binary).")
    log("NOT a speed ref: Python json, disk I/O on the timed path, or spawn-per-op.")
    log("ratio > 1 means ezjson slower than Rust. If MS=0 after raising N, no vs-rust claim.")
    fixtures = real_world_fixtures()
    for name, text, nbytes in fixtures:
        path = write_fixture("spd_" + name + ".json", text)
        n0 = 8 if nbytes >= 50000 else (20 if nbytes >= 5000 else 50)
        timeout = 300 if nbytes >= 50000 else 180

        log(f"\\n-- decode {name} ({nbytes}B) --")
        r_ez, p_ez, n_ez = run_bench_bump(DRV, ["bench-json-dec", path], n0, timeout)
        r_rs, p_rs, n_rs = run_bench_bump(RUST, ["bench-json-dec", path], n0, timeout)
        row = format_speed_row("json-dec", name, nbytes, r_ez, p_ez, n_ez, r_rs, p_rs, n_rs)
        log(row)
        speed_rows.append(row)

        log(f"\\n-- encode {name} ({nbytes}B) --")
        r_ez, p_ez, n_ez = run_bench_bump(DRV, ["bench-json-enc", path], n0, timeout)
        r_rs, p_rs, n_rs = run_bench_bump(RUST, ["bench-json-enc", path], n0, timeout)
        row = format_speed_row("json-enc", name, nbytes, r_ez, p_ez, n_ez, r_rs, p_rs, n_rs)
        log(row)
        speed_rows.append(row)

def format_speed_row(op, name, nbytes, r_ez, p_ez, n_ez, r_rs, p_rs, n_rs):
    if r_ez["timeout"] or r_rs["timeout"]:
        return f"TIMEOUT {op} {name} ez_n={n_ez} rust_n={n_rs}"
    if p_ez is None or p_rs is None:
        return (f"ERROR {op} {name} ez_rc={r_ez['rc']} rust_rc={r_rs['rc']} "
                f"ez_out={r_ez['out']!r} rust_out={r_rs['out']!r}")
    ez_per, ez_note = ms_per(p_ez, r_ez["wall"], n_ez)
    rs_per, rs_note = ms_per(p_rs, r_rs["wall"], n_rs)
    if p_ez["MS"] > 0 and p_rs["MS"] > 0 and rs_per > 0:
        ratio = ez_per / rs_per
        return (f"{op:9} {name:<14} {nbytes:7}B  "
                f"N_ez={n_ez:<5} N_rs={n_rs:<5}  "
                f"ezjson {ez_per:10.4f} ms/op ({ez_note})  "
                f"rust {rs_per:10.4f} ms/op ({rs_note})  "
                f"ratio {ratio:8.1f}x  "
                f"ez={r_ez['out'].strip()} | rs={r_rs['out'].strip()}")
    return (f"{op:9} {name:<14} {nbytes:7}B  "
            f"N_ez={n_ez:<5} N_rs={n_rs:<5}  "
            f"ezjson {ez_per:10.4f} ms/op ({ez_note}; no vs-rust claim)  "
            f"rust {rs_per:10.4f} ms/op ({rs_note})  "
            f"ez={r_ez['out'].strip()} | rs={r_rs['out'].strip()}")

def main():
    log("ezjson vs serde_json bench (Nix-embedded); Rust in-process reference")
    log(f"driver={DRV}")
    log(f"rust={RUST}")
    log(f"mode={MODE}")
    log("Speed ref: serde_json encode/decode timed inside one Rust process (N loops).")
    ping = ez(["ping"], 10)
    if ping["out"].strip() != "pong":
        log("FAIL: ezjson driver ping"); log(repr(ping)); sys.exit(2)
    log("ezjson driver ping ok (native ELF)")
    rping = rust(["ping"], 10)
    if rping["out"].strip() != "pong":
        log("FAIL: rust ref ping"); log(repr(rping)); sys.exit(2)
    log("rust serde_json ref ping ok")
    try:
        if MODE in ("correctness", "all"):
            correct_edges()
            correct_real()
        if MODE in ("speed", "all"):
            speed()
    except Exception:
        log("HARNESS EXCEPTION"); log(traceback.format_exc()); sys.exit(2)
    log(f"\\n== Summary: {fails} hard failure(s) of {len(cases)} cases ==")
    for c in cases:
        if c["status"] != "PASS" and c["hard"]:
            log(f"  FAIL {c['group']} | {c['name']}")
    if fails:
        sys.exit(1)
    log("ALL HARD CHECKS PASSED")

if __name__ == "__main__":
    main()
''
