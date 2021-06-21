#! /bin/bash
flake8 --extend-exclude "*SMTLIBv2*,*runtests.py*,__init__.py" src tests config bin/opfuzz bin/yinyang
