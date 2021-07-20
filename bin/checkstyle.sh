#! /bin/bash
flake8  --exclude "*SMTLIBv2*,*runtests.py*,__init__.py" src tests config bin/opfuzz bin/yinyang bin/typefuzz --select=E --ignore=E402 --statistics 
