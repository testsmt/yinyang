#! /bin/bash

pip uninstall antlr4-python3-runtime 
pip install -i https://test.pypi.org/simple/ yinyang

yinyang
opfuzz 
typefuzz 
exit 0
