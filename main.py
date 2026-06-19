get_uniqe_id = 0

def get_unique_id():
    global get_uniqe_id
    get_uniqe_id += 1
    return "P" + str(get_uniqe_id-1)

class Prop:
    def __init__(self,name : str):
        self.type = "prop"
        self.name = name
        self.args = tuple()
    
    def __mul__(self, other):
        res = Prop("")
        res.type = "and"
        res.args = (self, other)
        return res
        
    def __add__(self, other):
        res = Prop("")
        res.type = "or"
        res.args = (self, other)
        return res
    
    def __invert__(self):
        res = Prop("")
        res.type = "not"
        res.args = tuple([self])
        return res
    
    def __rshift__(self, other):
        res = Prop("")
        res.type = "imp"
        res.args = (self, other)
        return res
    
    
    def is_symbol(self):
        return self.type == "prop"
    
    def __str__(self):
        if self.is_symbol():
            return self.name
        else:
            if self.type == "and":
                return f"({self.args[0]} & {self.args[1]})"
            elif self.type == "or":
                return f"({self.args[0]} | {self.args[1]})"
            elif self.type == "not":
                return f"(~{self.args[0]})"
            elif self.type == "imp":
                return f"({self.args[0]} -> {self.args[1]})"
            else:
                raise SyntaxError("??????")
    
    def get_all_symbol(self):
        if self.is_symbol():
            return set([self.name])
        else:
            res = set()
            for arg in self.args:
                res |= arg.get_all_symbol()
            return res
    


class Sequent:
    def __init__(self, ant : tuple[Prop], suc : tuple[Prop]):
        self.ant = ant
        self.suc = suc
    
    def find_not_symbol(self):
        for i,p in enumerate(self.ant):
            if not p.is_symbol():
                return ("ant",i)
        for i,p in enumerate(self.suc):
            if not p.is_symbol():
                return ("suc",i)
        return ("none",-1)

    def get_id_seq(self):
        ind = self.find_not_symbol()

        if ind[0] == "none":
            return list([(self.ant, self.suc)])

        if ind[0] == "ant":
            i = ind[1]
            p = self.ant[i]
            if p.type == "and":
                S = Sequent(self.ant[:i] + (p.args[0], p.args[1]) + self.ant[i+1:], self.suc)
                return S.get_id_seq()
            elif p.type == "or":
                S1 = Sequent(self.ant[:i] + (p.args[0],) + self.ant[i+1:], self.suc)
                S2 = Sequent(self.ant[:i] + (p.args[1],) + self.ant[i+1:], self.suc)
                return S1.get_id_seq() + S2.get_id_seq()
            elif p.type == "not":
                S = Sequent(self.ant[:i] + self.ant[i+1:], self.suc + (p.args[0],))
                return S.get_id_seq()
            elif p.type == "imp":
                S = Sequent(self.ant[:i] + self.ant[i+1:], self.suc + (p.args[0],))
                S2 = Sequent(self.ant[:i] + (p.args[1],) + self.ant[i+1:], self.suc)
                return S.get_id_seq() + S2.get_id_seq()
            else:
                raise SyntaxError("??????")
        elif ind[0] == "suc":
            i = ind[1]
            p = self.suc[i]
            if p.type == "and":
                S1 = Sequent(self.ant, self.suc[:i] + (p.args[0],) + self.suc[i+1:])
                S2 = Sequent(self.ant, self.suc[:i] + (p.args[1],) + self.suc[i+1:])
                return S1.get_id_seq() + S2.get_id_seq()
            elif p.type == "or":
                S = Sequent(self.ant, self.suc[:i] + (p.args[0], p.args[1]) + self.suc[i+1:])
                return S.get_id_seq()
            elif p.type == "not":
                S = Sequent(self.ant + (p.args[0],) , self.suc[:i] + self.suc[i+1:])
                return S.get_id_seq()
            elif p.type == "imp":
                S = Sequent(self.ant + (p.args[0],) , self.suc[:i] + self.suc[i+1:])
                return S.get_id_seq()
            else:
                raise SyntaxError("??????")
        else:
            raise SyntaxError("???????")

    def check(self):
        res = S.get_id_seq()

        ans = True
        for Ant, Suc in res:
            tmp = set(y.name for y in Suc)
            res = False
            for x in [x.name for x in Ant]:
                if x in tmp:
                    res = True
                    break
            if not res:
                ans = False

        return ans

    def proof(self):
        ind = self.find_not_symbol()

        if ind[0] == "none":
            tmp = set(y.name for y in self.suc)
            intersect = None
            for x in set([x.name for x in self.ant]):
                if x in tmp:
                    intersect = x
                    break
            else:
                print([x.name for x in self.ant])
                print([y.name for y in self.suc])
                raise SyntaxError("??????")
            
            name = get_unique_id()
            print(f"auto {name} = Id<{intersect}>();")
            for x in self.ant:
                if x.name == intersect:
                    continue
                pre_name = name
                name = get_unique_id()
                print(f"auto {name} = KL<{x}>({pre_name});")
            for x in self.suc:
                if x.name == intersect:
                    continue
                pre_name = name
                name = get_unique_id()
                print(f"auto {name} = KR<{x}>({pre_name});")
            
            return name
            


        if ind[0] == "ant":
            i = ind[1]
            p = self.ant[i]
            if p.type == "and":
                S = Sequent(self.ant[:i] + (p.args[0], p.args[1]) + self.ant[i+1:], self.suc)
                pre_name = S.proof()
                name = get_unique_id()
                print(f"auto {name} = andL<{p.args[0]},{p.args[1]}>({pre_name});")
                return name
            elif p.type == "or":
                S1 = Sequent(self.ant[:i] + (p.args[0],) + self.ant[i+1:], self.suc)
                S2 = Sequent(self.ant[:i] + (p.args[1],) + self.ant[i+1:], self.suc)
                pre_name1 = S1.proof()
                pre_name2 = S2.proof()
                name = get_unique_id()
                print(f"auto {name} = orL<{p.args[0]},{p.args[1]}>({pre_name1}, {pre_name2});")
                return name
            elif p.type == "not":
                S = Sequent(self.ant[:i] + self.ant[i+1:], self.suc + (p.args[0],))
                pre_name = S.proof()
                name = get_unique_id()
                print(f"auto {name} = notL<{p.args[0]}>({pre_name});")
                return name
            elif p.type == "imp":
                S = Sequent(self.ant[:i] + self.ant[i+1:], self.suc + (p.args[0],))
                S2 = Sequent(self.ant[:i] + (p.args[1],) + self.ant[i+1:], self.suc)
                pre_name1 = S.proof()
                pre_name2 = S2.proof()
                name = get_unique_id()
                print(f"auto {name} = impL<{p.args[0]},{p.args[1]}>({pre_name1}, {pre_name2});")
                return name
            else:
                raise SyntaxError("??????")
        elif ind[0] == "suc":
            i = ind[1]
            p = self.suc[i]
            if p.type == "and":
                S1 = Sequent(self.ant, self.suc[:i] + (p.args[0],) + self.suc[i+1:])
                S2 = Sequent(self.ant, self.suc[:i] + (p.args[1],) + self.suc[i+1:])
                pre_name1 = S1.proof()
                pre_name2 = S2.proof()
                name = get_unique_id()
                print(f"auto {name} = andR<{p.args[0]},{p.args[1]}>({pre_name1}, {pre_name2});")
                return name
            elif p.type == "or":
                S = Sequent(self.ant, self.suc[:i] + (p.args[0], p.args[1]) + self.suc[i+1:])
                pre_name = S.proof()
                name = get_unique_id()
                print(f"auto {name} = orR<{p.args[0]},{p.args[1]}>({pre_name});")
                return name
            elif p.type == "not":
                S = Sequent(self.ant + (p.args[0],) , self.suc[:i] + self.suc[i+1:])
                pre_name = S.proof()
                name = get_unique_id()
                print(f"auto {name} = notR<{p.args[0]}>({pre_name});")
                return name
            elif p.type == "imp":
                S = Sequent(self.ant + (p.args[0],) , self.suc[:i] + self.suc[i+1:])
                pre_name = S.proof()
                name = get_unique_id()
                print(f"auto {name} = impR<{p.args[0]},{p.args[1]}>({pre_name});")
                return name
            else:
                raise SyntaxError("??????")
        else:
            raise SyntaxError("???????")
        
    def get_all_symbol(self):
        res = set()
        for p in self.ant:
            res |= p.get_all_symbol()
        for p in self.suc:
            res |= p.get_all_symbol()
        return res
    
    def get_proof(self):
        for p in self.get_all_symbol():
            print(f"Type {p};")
        print(f"print {self.proof()};")



A = Prop("A")
B = Prop("B")
C = Prop("C")


S = Sequent(((A>>B)*(B>>C)*(C>>A), ),((A>>C)*(C>>B)*(B>>A), ))
print(S.check())
print()

S.get_proof()



    


