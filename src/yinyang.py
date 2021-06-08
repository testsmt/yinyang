#! /usr/bin/python3.7
from src.args import args
from src.modules.Fuzzer import Fuzzer

def main():
    fuzzer = Fuzzer(args)
    fuzzer.run()

if __name__ == "__main__":
    main()
