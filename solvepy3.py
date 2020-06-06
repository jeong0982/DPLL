def make_formula(filename):
    f = open(filename)
    lines = f.readlines()
    flag = 0
    for line in lines:
        if (flag == 0):
            if line[0]