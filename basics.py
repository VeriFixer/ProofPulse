l1 = [1,2,3,4]
l2 = l1 
l1[0] = 5 
print(l1)
print(l2)

print(sum(l1))

l1.__reduce_ex__