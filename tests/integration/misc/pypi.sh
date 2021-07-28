#! /bin/bash

if ! pip uninstall -y antlr4-python3-runtime; then
    exit 1
fi

if ! pip install -i https://test.pypi.org/simple/ yinyang; then 
    exit 1
fi

yinyang
opfuzz 
typefuzz 
