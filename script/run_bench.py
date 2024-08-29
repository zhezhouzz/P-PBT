import subprocess
import json
import sys

bench_json = []

p_repo = ""

def mk_local_path(name):
    return "benchmarks/" + name

def mk_header_path(name):
    return mk_local_path(name) + "/HeaderSpec.p"

def mk_spec_path(name, specname):
    return mk_local_path(name) + "/" + specname + ".p"

def mk_output_path(pname):
    return p_repo + "/" + pname + "/PSyn/SynClient.p"

verbose = False

cmd_prefix = ["dune", "exec", "--", "bin/main.exe"]

def invoc_cmd(cmd, cwd=None):
    if (verbose):
        print(" ".join(cmd))
    try:
        subprocess.run(cmd, cwd=cwd)
    except subprocess.CalledProcessError as e:
        print(e.output)

def do_syn(option, name, specname):
    pname = ""
    for item in bench_json:
        if item["name"] == name:
            pname = item["p_repo"]
    if pname == "":
        print("no such benchmark")
        exit(1)
    header = mk_header_path(name)
    spec = mk_spec_path(name, specname)
    output = mk_output_path(pname)
    cmd = cmd_prefix + [option, header, spec, output]
    invoc_cmd(cmd)

if __name__ == '__main__':
    with open("script/benchmarks.json") as f:
        bench_json = json.load(f)
    try:
        if sys.argv[-1] == "verbose":
            verbose = True
    except:
        verbose = False
    p_repo = sys.argv[1]
    do_syn(sys.argv[2], sys.argv[3], sys.argv[4])
