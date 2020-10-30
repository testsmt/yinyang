import random
import string

def random_string(length=5):
    return ''.join(random.sample(string.ascii_letters + string.digits, length))

def plain(cli):
    plain_cli = ""
    for token in cli.split(" "):
        plain_cli += token.split("/")[-1]
    return escape(plain_cli)

def escape(s):
    s = s.replace(".", "")
    s = s.replace("=", "")
    return s

