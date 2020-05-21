class RV:

    def __init__(self,name,dist):
        self.name = name
        self.dist = dist

    def __str__(self):
        return str(self.dist)

    __repr__ = __str__

class Dist:

    def __init__(self,name,args):
        self.name = name
        self.args = args

    def __str__(self):
        s = ','.join(self.args)
        s = self.name + '(' + s + ')'
        return s     

    __repr__ = __str__

class Binomial(Dist):

    def __init__(self,name,args):
        self.name = name
        self.args = args
        self.n = args[0]
        self.p = args[1]

    def stan_sample(self):
        return 'binomial(' + ' ' + self.args[0] + ', ' + self.args[1] + ')'
        
    def stan_type(self):
        return 'int<lower = 0 , upper = ' + self.args[0] + '>'

    def lean_sample(self,rbits):
        if int(self.args[0]) == 1:
            s = 'generate_binomial_variate_simple(' + self.args[1] + ',(get u ' + str(rbits[0]) + '))'
        else:
            s = 'generate_binomial_variate_simple(' + self.args[0] + ',' + self.args[1] + ', (get u ' + str(rbits[0]) + '))'
        return s

    def lean_type(self):
        return (1, 'nat')
    
class Uniform(Dist):

    def __init__(self,name,args):
        self.name = name
        self.args = args
        self.a = args[0]
        self.b = args[1]

    def stan_sample(self):
        return 'uniform(' +  ' ' + self.args[0] + ', ' + self.args[1] + ')'
        
    def stan_type(self):
        return 'real<lower = ' + self.args[0] + ', upper = ' + self.args[1] + '>'

    def lean_sample(self,rbits):
        return 'generate_uniform_variate_simple(' +  self.args[0] + ',' + self.args[1] + ', (get u ' + str(rbits[0]) + '))'

    def lean_type(self):
        return (1,'nnreal')
    
class Beta(Dist):

    def __init__(self,name,args):
        self.name = name
        self.args = args
        self.alpha = args[0]
        self.beta = args[1]

    def stan_sample(self):
        return 'beta(' + ' ' + self.args[0] + ', ' + self.args[1] + ')'
        
    def stan_type(self):
        return 'real<lower = 0.0, upper = 1.0>'

    def lean_sample(self,rbits):
        return 'Beta ' + self.args

    def lean_type(self):
        return (1,'nat')
    
def make_dist(name,args):

    if name == 'Uniform':
        return Uniform(name,args)
    elif name == 'Beta':
        return Beta(name,args)
    elif name == 'Binomial':
        return Binomial(name,args)
    else:
        print('Unknown distribution: ', name)
        exit(1)
