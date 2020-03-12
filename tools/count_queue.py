import sys

if len(sys.argv) != 2:
  print("python cal_mask.py queue.csv")
  exit()

f1 = open(sys.argv[1], "r")

f1.readline()

num_tc = 0
num_10_tc = 0
num_20_tc = 0
num_30_tc = 0

for l in f1:
  l = l.strip()
  try:
    num_tc += 1
    num_fuzzed = int(l.split(",")[2])
    if num_fuzzed >= 5:
      num_10_tc += 1
    if num_fuzzed >= 10:
      num_20_tc += 1
    if num_fuzzed >= 15:
      num_30_tc += 1
  except :
    continue


print("total, 10, 20, 30")
print(",".join([str(num_tc),str(num_10_tc),str(num_20_tc),str(num_30_tc)]))
