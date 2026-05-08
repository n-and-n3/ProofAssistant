class Prop:
    def __init__(self,name : str):
        self.type = "prop"
        self.name = name
        self.args = tuple()
    
    def __and__(self, other):
        res = Prop("")
        res.type = "and"
        res.args = (self, other)
        return res
        
    def __or__(self, other):
        res = Prop("")
        res.type = "or"
        res.args = (self, other)
        return res
    
    def __invert__(self):
        res = Prop("")
        res.type = "not"
        res.args = tuple([self])
        return res
    
    def is_symbol(self):
        return self.type == "prop"
    
    def __str__(self):
        if self.is_symbol():
            return self.name
        else:
            return "".join([self.type, "(", ", ".join(map(str, self.args)) , ")"])
    


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
            else:
                raise SyntaxError("??????")
        else:
            raise SyntaxError("???????")

    def proof(self):
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


A = Prop("A")
B = Prop("B")
C = Prop("C")

X = ~ ( A | B )
Y = (~ A) & (~ B)

S = Sequent((X, ),(Y, ))
print(S.proof())



    


