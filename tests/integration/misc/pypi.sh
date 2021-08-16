#! /bin/bash

if ! pip uninstall -y antlr4-python3-runtime; then
    exit 1
fi

if ! pip install yinyang; then 
    exit 1
fi

yinyang

if [ $? -ne 2 ]; then
    exit 1
fi

opfuzz 

if [ $? -ne 2 ]; then
    exit 1
fi

typefuzz 

if [ $? -ne 2 ]; then
    exit 1
fi

sudo apt-get install -y cvc4 z3

cd ..
yinyang -o sat "z3 model_validate=true;cvc4 --check-models -m -i -q" yinyang/examples/phi1.smt2 yinyang/examples/phi2.smt2

if [ $? -eq 3 ]; then
    exit 1
fi

opfuzz "z3 model_validate=true;cvc4 --check-models -m -i -q" yinyang/examples/phi1.smt2

if [ $? -eq 3 ]; then
    exit 1
fi

typefuzz "z3 model_validate=true;cvc4 --check-models -m -i -q" yinyang/examples/phi1.smt2

if [ $? -eq 3 ]; then
    exit 1
fi
