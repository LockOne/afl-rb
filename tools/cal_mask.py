import sys

if len(sys.argv) != 2:
  print("python cal_mask.py mask.log")
  exit()

f1 = open(sys.argv[1], "r")

fuzz_mask_size = 0
total_byte_size = 0
num_branch = 0
num_0_branch = 0

for l in f1:
  l = l.strip()
  fuzz_mask_size += float(l.split("/")[0])
  total_byte_size += float(l.split("/")[1])
  num_branch += 1
  if l.split("/")[0] == "0.0":
    num_0_branch += 1

print ("total : ")
print (str(fuzz_mask_size) + "/" + str(total_byte_size))

print ("total 0 branch num : " + str(num_0_branch))
print ("total branch num : " + str(num_branch))
print ("avg: ")
print (str(fuzz_mask_size // num_branch) + "/" + str(total_byte_size // num_branch) + \
         " (" + str(fuzz_mask_size / total_byte_size * 100.0) + "%)")
