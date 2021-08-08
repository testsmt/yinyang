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

