import random

def ask(arr):
    print("?",*arr,flush=True)
    res = list(map(int,input().split()))
    return res


T = int(input())

for _ in range(T):
    N = int(input())
    A = [random.randrange(2) for _ in range(N-1)]
    
    ans = [-1]*N


    for _ in range(10):
        P = ask(A)
        res = [-1]*N
        for i in range(N):
            if i == 0:
                res[i] = P[i]
            elif P[i-1] != P[i]:
                res[i] = P[i]
            else:
                pass
        for i in range(N-1):
            if res[i] != -1 and res[i+1] == -1:
                A[i] = 1-A[i]
            else:
                A[i] = random.randrange(2)
        ans = [(ans[i] if ans[i] != -1 else res[i]) for i in range(N)]

        if ans.count(-1) == 0:
            break

    print("!",*ans,flush=True)




