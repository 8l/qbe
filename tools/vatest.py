# generate variadic calls to test the
# abi implementation

from random import seed, randint, uniform
from struct import unpack

I, D = 'd', 'g'

formats = [
	# list of format to tests
	[I],
	[D],
	[I,D],
	[D,D],
	[I,I,I,I],
	[D,D,D,D],
	[I,D,I,D],
	[D,D,I,I],
	[I,I,D,D],
	[],
]

generate = [
	# numbers of fixed integer and
	# floating point arguments to
	# test
	(0, 0), (1, 0), (0, 1), (4, 0),
	(0, 6), (5, 7), (10, 10),
]

def mkargs(nargs, type, name):
	args = map(
		lambda n: ''.join([type, name, str(n), ', ']),
		range(nargs)
	)
	return ''.join(args)

def mkfstr(fmt):
	fstr = map(
		lambda x: {I: '%d ', D: '%g '}[x],
		fmt
	)
	return '"' + ''.join(fstr) + '\\n"'

def randargs(fmt):
	ra = {
		I: lambda: '{}'.format(randint(-10, 10)),
		D: lambda: '{0:.4g}'.format(uniform(-10, 10))
	}
	return list(map(lambda x: ra[x](), fmt))

def genssa(qbeprint, qbecall):
	funcs = [('qbeprint', qbeprint), ('qbecall', qbecall)]
	for fnum, (nia, nfa) in enumerate(generate):
		params = "{}{}l %fmt, ...".format(
			mkargs(nia, 'w ', '%argw'),
			mkargs(nfa, 'd ', '%argd')
		)
		for name, code in funcs:
			print('export function ${}{}({}) {}'
				.format(name, fnum, params, code)
			)

def gendriver():
	print('# >>> driver')
	print('# #include <stdio.h>')

	for fnum, (nia, nfa) in enumerate(generate):
		params = "{}{}char *, ...".format(
			mkargs(nia, 'int ', 'argw'),
			mkargs(nfa, 'double ', 'argd')
		)
		for name in ['qbeprint', 'qbecall']:
			print('# extern void {}{}({});'
				.format(name, fnum, params)
			)

	output = ''
	print('# int main() {')

	for fnum, (nia, nfa) in enumerate(generate):
		info = '# ({} int, {} double)'.format(nia, nfa)
		print('# 	puts("{}");'.format(info))
		output += '# {}\n'.format(info)
		for fmt in formats:
			ra = randargs(fmt)
			vaargs = ', '.join(ra)
			expect = ' '.join(ra)
			if fmt:
				vaargs = ', ' + vaargs
				expect = expect + ' '
			args = ''.join(
				['0, '] * (nia+nfa) +
				[mkfstr(fmt), vaargs]
			)
			for name in ['qbeprint', 'qbecall']:
				print('# 	{}{}({});'
					.format(name, fnum, args)
				)
				output += '# {}\n'.format(expect)

	print('# }')
	print('# <<<')

	print('\n# >>> output\n' + output + '# <<<')


qbeprint="""{{
@start
	%fmtdbl =l alloc4 4
	%fmtint =l alloc4 4
	%emptys =l alloc4 4
	storew {}, %fmtint
	storew {}, %fmtdbl
	storew 0, %emptys
	%vp =l alloc8 24
	%fmt1 =l add 1, %fmt
	vastart %vp
@loop
	%p =l phi @start %fmt1, @casef %p1, @cased %p1
	%c =w loadsb %p
	%p1 =l add 3, %p
	jnz %c, @loop1, @end
@loop1
	%isg =w ceqw %c, 103
	jnz %isg, @casef, @cased
@casef
	%dbl =d vaarg %vp
	call $printf(l %fmtdbl, d %dbl, ...)
	jmp @loop
@cased
	%int =w vaarg %vp
	call $printf(l %fmtint, w %int, ...)
	jmp @loop
@end
	call $puts(l %emptys)
	ret
}}
""".format(
	unpack("i", b'%d \x00')[0],
	unpack("i", b'%g \x00')[0]
)

qbecall="""{
@start
	%vp =l alloc8 24
	vastart %vp
	call $vprintf(l %fmt, l %vp)
	ret
}
"""


if __name__ == "__main__":
	seed(42)
	genssa(qbeprint, qbecall)
	gendriver()
