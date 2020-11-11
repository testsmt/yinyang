import argparse
import os

from src.utils import random_string
from src.modules.OptionGenerator import OptionGenerator
from config.config import solvers

rootpath = "/".join(__file__.split('/')[:-2])

parser = argparse.ArgumentParser()
parser.add_argument(
    "SOLVER_CLIS",
    help="solvers' command-line interfaces for solving .smt2 files"
)
parser.add_argument(
    "PATH_TO_SEEDS",
    nargs='+',
    help="path to the seed files/folders"
)
parser.add_argument(
    "-s","--strategy",
    choices=["opfuzz", "fusion"],
    default="opfuzz",
    help="set fuzzing strategy"
)
parser.add_argument(
    "-o","--oracle",
    choices=["sat", "unsat"],
    default="unknown",
    help="set oracle for semantic fusion strategy (default: unknown)"
)
parser.add_argument(
    "-i", "--iterations",
    type=int,
    help="set mutating iterations for each seed/pair (default: 300 for Type-Aware Operator Mutation, 30 for SemanticFusion)"
)
# parser.add_argument(
#     "-m", "--modulo",
#     type=int,
#     default=2,
#     help="determines when the mutant will be forwarded to the solvers"
# )
parser.add_argument(
    "-t", "--timeout",
    default=8,
    type=int,
    help="set timeout for solving process (default: 8)"
)
parser.add_argument(
    "-optfuzz","--optfuzz",
    default="",
    help="read solvers' option setting and enable option fuzzing"
)
parser.add_argument(
    "-name","--name",
    default=random_string(),
    help="set name of this fuzzing instance (default: random string)"
)
parser.add_argument(
    "-bugs","--bugsfolder",
    default=rootpath+"/bugs",
    help="set bug folder (default: "+rootpath+"/bugs)"
)
parser.add_argument(
    "-scratch","--scratchfolder",
    default=rootpath+"/scratch",
    help="set scratch folder (default: "+rootpath+"/scratch)"
)
# parser.add_argument(
#     "-opconfig","--opconfig",
#     default=rootpath+"/config/operator_mutations.txt",
#     help="set operator mutation configuration (default: "+rootpath+"/config/operator_mutations.txt)"
# )
# parser.add_argument(
#     "-fusionfun","--fusionfun",
#     default=rootpath+"/config/fusion_functions.txt",
#     help="set fusion function configuration (default: "+rootpath+"/config/fusion_functions.txt)"
# )
parser.add_argument(
    "-km", "--keep-mutants",
    action='store_true',
    help="Do not delete the mutants generated in the scratchfolder."
)
args = parser.parse_args()

# pre-processing
if args.SOLVER_CLIS == "":
    args.SOLVER_CLIS = solvers
else:
    args.SOLVER_CLIS = args.SOLVER_CLIS.split(";") + solvers


if args.timeout <= 0: exit("Error: timeout should not be a negative number or zero.")

if not args.iterations:
    if args.strategy == "opfuzz":
        args.iterations = 300
    else:
        args.iterations = 30

if args.iterations <= 0: exit("Error: iterations should not be a negative number zero.")

if not os.path.isdir(args.bugsfolder):
    try:
        os.mkdir(args.bugsfolder)
    except Exception as e:
        print(e)
        exit(0)

if not os.path.isdir(args.scratchfolder):
    try:
        os.mkdir(args.scratchfolder)
    except Exception as e:
        print(e)
        exit(0)

# if not os.path.isfile(args.fusionfunctions) and (args.strategy == "fusion" or args.strategy == "mix"):
#     exit("Error: File for fusion functions %s not exist" %(args.fusionfunctions))

temp_seeds = []
for path in args.PATH_TO_SEEDS:
    if not os.path.exists(path):
        exit("Error: %s does not exist" % (path))
    if os.path.isfile(path):
        temp_seeds.append(path)
    elif os.path.isdir(path):
        for subdir, dirs, files in os.walk(path):
            for filename in files:
                filepath = subdir + os.sep + filename
                if filepath.endswith(".smt2"):
                    temp_seeds.append(filepath)
    else:
        exit("Error: %s is neither a file nor a directory")
args.PATH_TO_SEEDS = temp_seeds

if args.optfuzz == "":
    args.optfuzz = None
else:
    args.optfuzz = OptionGenerator(args.optfuzz)
