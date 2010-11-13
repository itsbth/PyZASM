def strlen(str):
    i = 0
    while str[i] != 0:
        i = i + 1
    return i


def main():
    i = 0
    while 1:
        i = strlen("Hello, World!")
        "mov @i,port0;"