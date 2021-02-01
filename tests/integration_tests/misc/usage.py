"""
Integration test for usage part in README.md. 
""" 
import os,subprocess
import sys
import random
sys.path.append("../../../")


import src.parsing.timeout_decorator

python=sys.executable

def run_opfuzz(first_config, second_config, directory, opts, timeout):
    @exit_after(timeout_limit)
    def _run_opfuzz(first_config, second_config, directory, opts):
        cmd = python+' yinyang.py '+ '"'+ first_config+ ";" + second_config + '" ' + opts + ' ' + directory 
        output = subprocess.getoutput(cmd)
        soundness_issues=None
        crash_issues = None
        # TODO:Add more 
        for line in output.split("\n"):
            if "Soundness" in line:
                soundness_issues = int(line.split()[-1])
            if "Crash" in line:
                crash_issues = int(line.split()[-1])
        return soundness_issues, crash_issues, cmd

    _run_opfuzz(first_config, second_config, directory, opts)

# get most recent releases of cvc4 and z3.  
def get_cvc4():
    cvc4_link = "https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt"
    subprocess.getoutput("wget "+cvc4_link)
    subprocess.getoutput("chmod +x cvc4-1.7-x86_64-linux-opt")
    return os.path.abspath("cvc4-1.7-x86_64-linux-opt")

def get_z3():
    z3_link= "https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip"
    subprocess.getoutput("wget "+z3_link)
    # TODO:
    subprocess.getoutput("unzip z3-4.8.6-x64-ubuntu-16.04.zip")
    return os.path.abspath("z3-4.8.6-x64-ubuntu-16.04/bin/z3")

# 1. Get SMT-LIB 2 benchmarks.
benchmarks=\
"""
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/ABVFP.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/ALIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/AUFBVDTLIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/AUFDTLIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/AUFLIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/AUFLIRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/AUFNIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/AUFNIRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/BV.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/BVFP.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/FP.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/LIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/LRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/NIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/NRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_ABV.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_ABVFP.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_ALIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_ANIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_AUFBV.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_AUFLIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_AUFNIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_AX.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_BV.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_BVFP.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_BVFPLRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_DT.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_FP.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_FPLRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_IDL.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LIRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_NIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_NIRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_NRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_RDL.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_S.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_SLIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_UF.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_UFBV.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_UFIDL.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_UFLIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_UFLRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_UFNIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_UFNRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/UF.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/UFBV.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/UFDT.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/UFDTLIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/UFDTNIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/UFIDL.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/UFLIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/UFLRA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/UFNIA.git
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/ABVFP.git incremental/ABVFP
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/ALIA.git incremental/ALIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/ANIA.git incremental/ANIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/AUFNIRA.git incremental/AUFNIRA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/BV.git incremental/BV
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/BVFP.git incremental/BVFP
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/LIA.git incremental/LIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/LRA.git incremental/LRA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_ABV.git incremental/QF_ABV
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_ABVFP.git incremental/QF_ABVFP
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_ALIA.git incremental/QF_ALIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_ANIA.git incremental/QF_ANIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_AUFBV.git incremental/QF_AUFBV
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_AUFBVLIA.git incremental/QF_AUFBVLIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_AUFBVNIA.git incremental/QF_AUFBVNIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_AUFLIA.git incremental/QF_AUFLIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_BV.git incremental/QF_BV
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_BVFP.git incremental/QF_BVFP
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_FP.git incremental/QF_FP
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_LIA.git incremental/QF_LIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_LRA.git incremental/QF_LRA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_NIA.git incremental/QF_NIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_UF.git incremental/QF_UF
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_UFBV.git incremental/QF_UFBV
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_UFBVLIA.git incremental/QF_UFBVLIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_UFLIA.git incremental/QF_UFLIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_UFLRA.git incremental/QF_UFLRA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/QF_UFNIA.git incremental/QF_UFNIA
# git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks-inc/UFLRA.git incremental/UFLRA
"""

print("1. Get SMT-LIB 2 benchmarks", flush=True)
k = random.randint(0,len(benchmarks.split("\n")) -1) 
benchmark = benchmarks.split("\n")[k]
cmd = benchmark[1:] + " chosen_logic"


print("2. Get and build SMT solvers.",flush=True)
get_z3()
get_cvc4()

print("3. Run Yin-Yang on the benchmarks e.g. with Z3 and CVC4.", flush=True)
first_config="z3 model_validate=true"
second_config="cvc4 --check-models --produce-models --incremental -q"
run_opfuzz(first_config, second_config, "chosen_logic","",30)
