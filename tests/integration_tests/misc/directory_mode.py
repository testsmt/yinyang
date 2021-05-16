import os
import sys
import random
import subprocess

python=sys.executable

TIME_LIMIT=180

def run_opfuzz(first_config, second_config, directory, opts, timeout_limit):
    timeout="timeout --signal=INT "+str(timeout_limit)+" "
    cmd = timeout+python+' yinyang.py '+ '"'+ first_config+ ";" + second_config + '" ' + opts + ' ' + directory
    output = subprocess.getoutput(cmd)
    generated_seeds = 0
    used_seeds = 0
    ignored_issues = 0
    for line in output.split("\n"):
        if "Generated mutants" in line:
            generated_seeds = int(line.split()[-1])
        if "Used seeds" in line:
            used_seeds = int(line.split()[-1])
        if "Ignored" in line:
            ignored_issues = int(line.split()[-1])

    return generated_seeds, used_seeds, ignored_issues, cmd

def get_cvc4():
    cvc4_link = "https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt"
    os.system("wget "+cvc4_link)
    subprocess.getoutput("chmod +x cvc4-1.8-x86_64-linux-opt")
    return os.path.abspath("cvc4-1.8-x86_64-linux-opt")

def get_z3():
    z3_link= "https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip"
    os.system("wget "+z3_link)
    os.system("unzip z3-4.8.10-x64-ubuntu-18.04.zip")
    return os.path.abspath("z3-4.8.10-x64-ubuntu-18.04/bin/z3")

def cleanup():
    subprocess.getoutput("rm -rf cvc4*")
    subprocess.getoutput("rm -rf z3*")

cleanup()
cvc4 = get_cvc4()
z3 = get_z3()
first_config=z3+" model_validate=true"
second_config=cvc4+" --check-models --produce-models --incremental -q"
mock_benchmarks=str(os.path.dirname(os.path.realpath(__file__)))+"/mock_benchmarks"
generated_seeds, used_seeds, ignored_issues, cmd = run_opfuzz(first_config, second_config, mock_benchmarks ,"-m 1",TIME_LIMIT)
if not (generated_seeds == 300 and used_seeds == 3 and ignored_issues == 2):
    print("An error occurred.", flush=True)
    print("cmd", cmd)
    print("generated_seeds", generated_seeds)
    print("used_seeds", used_seeds)
    print("ignored_issues", ignored_issues)
    exit(1)
