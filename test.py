aritys = {"and" : 2, "or" : 2, "not" : 1}

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
    
    def __str__(self):
        if self.type == "prop":
            return self.name
        else:
            return "".join([self.type, "(", ", ".join(map(str, self.args)) , ")"])

    

A = Prop("A")
B = Prop("B")
C = Prop("C")

print(A, B, C)

X = (A & B) | C

print(X)

