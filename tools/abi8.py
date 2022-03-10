#!/usr/bin/python3

# support script to create
# the abi8.ssa test

def ctype(arg):
    if arg[0] == 'p': return ctype(arg[1:])
    if arg[0] == ':': return 'S' + arg[1:]
    return {'w':'int', 'l':'long',
            's':'float', 'd':'double'}[arg]

def cparam(iarg):
    return ctype(iarg[1]) + ' p' + str(iarg[0])

def gencfn(id, args):
    out = '# extern void qfn' + id + '('
    out += ', '.join(map(ctype, args)) + ');\n'
    out += '# void cfn' + id + '('
    out += ', '.join(map(cparam, enumerate(args)))
    out += ') {\n'
    out += '# \tprintf("qbe->c(%d)", ' + id + ');\n'
    out += '# \t'
    for (i, arg) in enumerate(args):
        if arg[0] != 'p': continue
        ty = arg[1:]
        if ty[0] == ':':
            out += 'p' + ty[1:] + '(&'
        else:
            out += 'p' + ty + '('
        out += 'p' + str(i) + '); '
    out += 'puts("");\n'
    out += '# \tqfn' + id +  '('
    out += ', '.join('p'+str(i) for i in range(len(args)))
    out += ');\n'
    out += '# }\n'
    return out

def qparam(iarg):
    ty = iarg[1][1:] if iarg[1][0] == 'p' else iarg[1]
    return ty + ' %p' + str(iarg[0])

def genqfn(id, args):
    out = 'export\nfunction $qfn' + id + '('
    out += ', '.join(map(qparam, enumerate(args)))
    out += ') {\n'
    out += '@start\n'
    out += '\t%r0 =w call $printf(l $ctoqbestr, w ' + id + ')\n'
    for (i, arg) in enumerate(args):
        if arg[0] != 'p': continue
        ty = arg[1:]
        if ty[0] == ':':
            out += '\tcall $p' + ty[1:]
            out += '(l %p' + str(i) + ')\n'
        else:
            out += '\tcall $p' + ty
            out += '(' + ty + ' %p' + str(i) + ')\n'
    out += '\t%r1 =w call $puts(l $emptystr)\n'
    out += '\tret\n'
    out += '}\n'
    return out

def carg(iarg):
    i, arg = iarg
    print = arg[0] == 'p'
    ty = arg if not print else arg[1:]
    if ty[0] == ':':
        if print:
            return ty + ' $' + ty[1:]
        else:
            return ty + ' $z' + ty[1:]
    if not print:
        return ty + ' 0'
    if ty == 'w' or ty == 'l':
        return ty + ' ' + str(i+1)
    if ty == 's' or ty == 'd':
        flt = str(i+1) + '.' + str(i+1)
        return ty + ' ' + ty + '_' + flt

def genmaincall(id, args):
    out = '\tcall $cfn' + id + '('
    out += ', '.join(map(carg, enumerate(args)))
    out += ')\n'
    return out

def gen(tvec):
    for i, t in enumerate(tvec):
        print(genqfn(str(i), t), end='')
    print('')
    for i, t in enumerate(tvec):
        print(genmaincall(str(i), t), end='')
    print('')
    for i, t in enumerate(tvec):
        print(gencfn(str(i), t), end='')

TVEC = [
   ['s']*8 + ['ps'],
   ['pw', 'ps', 'p:fi1'],
   ['pw', 'p:fi2', 'ps'],
   ['pw', 'ps', 'p:fi3'],
   ['p:ss'],
   ['d']*7 + ['p:ss', 'ps', 'pl'],
   ['p:lb'],
   ['w']*7 + ['p:lb'],
   ['w']*8 + ['p:lb'],
   [ 'p:big' ],
   ['w']*8 + ['p:big', 'ps', 'pl'],
]

if __name__ == '__main__':
    gen(TVEC)
