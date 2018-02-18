import re

casere = re.compile("\s*case class ([A-Za-z]+) *\(([^)]*)\).*")
argre = re.compile("\s*([A-Za-z]+)\s*:\s*([A-Za-z]+(?:\[[A-Za-z ,]+\])?)\s*")
clazzes = []
with open("astnodes.txt") as f:
    for line in f:
        match = casere.match(line)
        if match:
            name = match.group(1)
            args = []
            arglst = match.group(2).split(',')
            for arg in arglst:
                match = argre.match(arg)
                if match:
                    args.append((match.group(1), match.group(2)))
            clazzes.append((name, args))

print()
for clazz in sorted(clazzes):
    print('case {0}({1}) => d({1})'.format(clazz[0], ", ".join(map(lambda x: x[0], clazz[1]))))
print()
print()
for clazz in sorted(clazzes):
    print('case "{0}" => {0}({1})()'.format(clazz[0], ", ".join(map(lambda x: 'p[{}]() /* {} */'.format(x[1], x[0]), clazz[1]))))
