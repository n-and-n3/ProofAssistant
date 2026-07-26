import random
from functools import cache

#P = list(range(2000))

cnt = 0
# P[i]+P[j] > P[k] ? 
@cache
def ask(i,j,k):
    global cnt
    if i == k or j == k:
        return True
    if cnt >= 25000:
        exit()
    print("?",i+1,j+1,k+1,flush=True)
    res = input()
    cnt += 1
    #res = "Yes" if (P[i] + P[j] > P[k]) else "No"
    #print(res)
    if res == "Yes":
        return True
    elif res == "No":
        return False
    else:
        exit()


N = int(input())
#N = len(P)

arr = list(range(N))

while len(arr) > 1:
    m = -1
    while True:
        x,y = random.sample(arr, 2)
        r = ask(x,x,y)
        if not r:
            m = x
            break
    arr_ = []
    elim = []
    for a in arr:
        r = ask(m,m,a)
        if r:
            arr_.append(a)
    arr = arr_

ind1 = arr[0]

def ge(x,y):
    return ask(x,ind1,y)

def msort(arr):
    L = len(arr)
    if L <= 1:
        return arr
    F = msort(arr[:L//2])
    B = msort(arr[L//2:])
    res = []
    i = 0
    j = 0
    while i < len(F) and j < len(B):
        if ge(F[i], B[j]):
            res.append(B[j])
            j += 1
        else:
            res.append(F[i])
            i += 1
    while i < len(F):
        res.append(F[i])
        i += 1
    while j < len(B):
        res.append(B[j])
        j += 1
    return res


res = msort(list(range(N)))
ans = [-1]*N
for i in range(N):
    ans[res[i]] = i+1

print("!",*ans)




