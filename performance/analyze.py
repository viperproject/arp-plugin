import sys
import csv

DEL_START = 5
DEL_END = 5

def avg(l):
    return sum(l)/len(l)

def main():
    if len(sys.argv) < 3:
        print("usage: {} path/to/timings.csv path/to/analyzed.csv".format(sys.argv[0]))
        return
    with open(sys.argv[1], newline="") as csvfile:
        rd = csv.DictReader(csvfile, delimiter=';')
        timings = {}
        code = {}
        for row in rd:
            key = (row['input file'], row['run configuration'])
            if key not in timings:
                timings[key] = []
                code[key] = (set([int(row['exit code'])]), row['timeout'])
            timings[key].append(float(row['runtime [s]']))
            code[key][0].add(int(row['exit code']))
        with open(sys.argv[2], "w", newline="") as csvout:
            wr = csv.writer(csvout, delimiter=';')
            wr.writerow(["file", "config", "return code", "timeout", "min time", "max time", "avg", "clean avg"])
            for key in sorted(timings.keys()):
                lst = timings[key]
                lst.sort()
                wr.writerow([key[0], key[1], ", ".join(map(str, code[key][0])), code[key][1], min(lst), max(lst), avg(lst), avg(lst[DEL_START:-DEL_END])])

if __name__ == '__main__':
    main()
