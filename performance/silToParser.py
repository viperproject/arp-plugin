import sys
import os

def main():
    if len(sys.argv) < 3:
        print("usage: {} indir outdir".format(sys.argv[0]))
        return

    if not os.path.exists(sys.argv[2]):
        os.makedirs(sys.argv[2])

    for infile in os.listdir(sys.argv[1]):
        print(infile)
        os.system("java -Xss64m -jar silicon.jar --plugin PerformanceParserExport {} > {}".format(os.path.join(sys.argv[1], infile), os.path.join(sys.argv[2], infile)))

if __name__ == '__main__':
    main()
