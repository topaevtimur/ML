fin = open("proof3.in", "r")
fout = open("proof3.out", "w")

line = fin.readline().rstrip()
ab = line.split()
a = int(ab[0])
b = int(ab[1])
c = b - a

if c >= 0:
    A = B = C = "0"
    for i in range(0, b):
        if i < c:
            C += "'"
        if i < a:
            A += "'"
        B += "'"
    print("|-?p(" + A + "+p)=" + B, end="\n", file=fout)
    froot = open("Proofs/part11.proof", "r")
    expr_list = froot.readlines()
    froot.close()
    for i in range(len(expr_list)):
        print(expr_list[i], end="", file=fout)
    print("@a(a+0=a)->" + A + "+0=" + A, end="\n", file=fout)
    print(A + "+0=" + A, end="\n", file=fout)
    fpart = open("Proofs/part12.proof", "r")
    part = fpart.readlines()
    fpart.close()
    S = ""
    for i in range(len(part)):
        S += part[i].replace("A", A)
    S += "\n"
    st = ""
    for i in range(0, c):
        print(S.replace('#', st), end="", file=fout)
        st += "'"
    print("(" + A + "+" + C + ")=" + B + "->?p(" + A + "+p)=" + B + "\n" + "?p(" + A + "+p)=" + B, end="\n", file=fout)
else:
    A = B = "0"
    for i in range(0, a):
        A += "'"
        if i < b:
            B += "'"
    print("|-!?p(" + A + "+p)=" + B, file=fout)
    froot = open("Proofs/part21.proof", "r")
    expr_list = froot.readlines()
    froot.close()
    for i in range(len(expr_list)):
        print(expr_list[i], end="", file=fout)
    print(file=fout)
    c *= -1
    C = B = ""
    for i in range(0, c - 1):
        if i < b:
            B += "'"
        C += "'"
    for i in range(c - 1, b):
        B += "'"
    fpart = open("Proofs/part22.proof", "r")
    part = fpart.readlines()
    fpart.close()
    for i in range(len(part)):
        s = part[i].replace("C", C)
        s = s.replace("B", B)
        s = s.replace(" ", "")
        print(s, end="", file=fout)
fin.close()
fout.close()
