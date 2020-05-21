# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

from inspect import *
from functools import partial
import ast
import astpretty
import parser
import _ast
import dis
import types
from relax.primitives import *

class StackList(list):
    def push(self, item):
        self.append(item)

class LOOPMARKER:

    def __init__(self,ptr):
        self.ptr = ptr
    
    def __str__(self):
        return 'GOTO: ' + str(self.ptr)

    __repr__ = __str__
    

def concolic_vm(model,debug=0):

    # Currently, all the code must come from the same python module
    module = getmodule(model)
    functions_list =  getmembers(module,isfunction)
    fmap = {}

    for (name,code) in functions_list:
        fmap[name] = code
    
    rvmap = {}

    pro_tips = []
    handled = []

    def interpreter(model,debug = 0):

        closure = getclosurevars(model).nonlocals

        if 'pro_tip' in closure:
            tips = closure['pro_tip']
            tip_type = tips[0]
            if tip_type == 'STAN_NUTS':
                param = tips[1]
                if not param[0] in handled:
                    pro_tips.append(closure['pro_tip'])
                    handled.extend(param)
            elif tip_type == 'Block':
                pro_tips.append(closure['pro_tip'])
            else:
                print('Unknown tip', tip_type)
                exit(0)

        if debug >= 1:
            print('Start: ', model.__name__, ' with path ', closure['path'])

        # Local evaluation stack, contains both symbolic and real values
        stack = StackList([])
        # Local variables binding
        varmap = {}

        ret = ''

        code = []
        for ins in dis.get_instructions(model):
            code.append(ins)

        code_pointer = 0

        while(True):

            ins = code[code_pointer]
            op = ins.opname
            arg = ins.argval

            if debug >= 2:
                print('')
                print(op, ' ', arg)

            if (op == 'LOAD_DEREF'):
                v = closure[arg]
                stack.push(v)
            elif (op == 'LOAD_GLOBAL'):
                stack.push(arg)
            elif (op == 'CALL_FUNCTION'):
                l = []
                l_obj = []
                for i in range(arg):
                    a = stack.pop()
                    l.append(str(a))
                    l_obj.append(a)
                l.reverse()
                l_obj.reverse()
                a = stack.pop()
                if arg != 0:
                    # Symbolic call
                    if a == 'sample':
                        # Pyro sample, execute RV path
                        name = l[0]
                        dist = l_obj[1]
                        rv = RV(name,dist)
                        stack.push(rv)
                    elif(a in fmap):
                        if len(l) == 2:
                            #savepath = l[0]
                            stack.push(fmap[a](l[0],eval(l[1])))
                        elif len(l) == 3:
                            #savepath = l[1]
                            stack.push(fmap[a](l[0],l[1],eval(l[2])))
                        else:
                            print('Not working with more than 3 arguments yet (0)')
                            exit(0)
                    elif(type(a) == types.FunctionType):
                        if len(l) == 2:
                            #savepath = l[0]
                            stack.push(a(l[0],eval(l[1])))
                        elif len(l) == 3:
                            #savepath = l[1]
                            stack.push(a(l[0],l[1],eval(l[2])))
                        else:
                            print('Not working with more than 3 arguments yet (1)', len(l))
                            exit(0)
                    else:
                        dist = make_dist(str(a),l)
                        stack.push(dist)
                else:
                    # Actual model execution
                    if debug >= 2:
                        print('To execute: ', a)
                    (ret,_) = interpreter(a,0)
                    stack.push(ret)
            elif (op == 'UNPACK_SEQUENCE'):
                a = stack.pop()
                for i in range(arg):
                    stack.push(a[i])
            elif (op == 'STORE_FAST'):
                a = stack.pop()
                # Handling loops. That seems crazy but that's not me!
                if type(a) == LOOPMARKER:
                    code_pointer = a.ptr - 1
                else:
                    # Normal case
                    varmap[arg] = a
                    if type(a) == RV:
                        rvmap[a.name] = a
            elif (op == 'LOAD_FAST'):
                if type(varmap[arg]) == RV:
                    stack.push(varmap[arg].name)
                else:
                    stack.push(varmap[arg])
            elif (op == 'LOAD_CONST'):
                stack.push(arg)
            elif (op == 'BINARY_ADD'):
                a1 = stack.pop()
                a2 = stack.pop()
                stack.push(a2 + a1)
            elif (op == 'BINARY_MULTIPLY'):
                a1 = stack.pop()
                a2 = stack.pop()
                stack.push(str(a2) + ' * ' + str(a1))
            elif (op == 'BINARY_SUBSCR'):
                a1 = stack.pop()
                a2 = stack.pop()
                if (type(a2) == str):
                    stack.push(str(a2) + '[' + str(a1) + ']')
                else:
                    stack.push(a2[a1])
            elif (op == 'BUILD_LIST'):
                l = []
                for i in range(arg):
                    a = stack.pop()
                    l.append(a)
                stack.push(l)
            elif (op == 'SETUP_LOOP'):
                stack.push(LOOPMARKER(arg // 2))
            elif (op == 'LOAD_ATTR'):
                pass
            elif (op == 'CALL_FUNCTION_KW'):
                pass
            elif (op == 'GET_ITER'):
                a = stack.pop()
                stack.push(iter(a))
            elif (op == 'FOR_ITER'):
                a = stack.pop()
                for i in a:
                    stack.push(i)
            elif (op == 'POP_TOP'):
                stack.pop()
            elif (op == 'JUMP_ABSOLUTE'):
                code_pointer = (arg // 2)
            elif (op == 'POP_BLOCK'):
                pass
            elif (op == ''):
                pass
            elif (op == 'RETURN_VALUE'):
                if debug >=1:
                    print('End: ', model.__name__)
                a = stack.pop()
                assert(stack == [])
                if a == None:
                    return ([],varmap)
                else:
                    l = []
                    for rv in a:
                        l.append(rvmap[rv])   
                    return (l,varmap)
            else:
                print('Not implemented: ', op)
                exit(0)

            code_pointer += 1

            if debug >= 2:
                print('stack: ', stack)
                print('map: ', varmap)
                print('rvs', rvmap)

    interpreter(model,debug)
                
    return (rvmap,pro_tips)

def run_and_print(model,debug=0):
    
    (rvmap,_) = concolic_vm(model,0)
    for rv in rvmap:
        print(rv, '~',rvmap[rv])    

def get_blocks(rvmap,pro_tips):
    rvs = rvmap.keys()
    blocks = []
    for tip in pro_tips:
        tip_type = tip[0]
        if tip_type == 'Block':
            for suffix in tip[1]:
                l = []
                for rv in rvs:
                    if rv.endswith(suffix):
                        l.append(rv)
                blocks.append(l)
        else:
            continue
    return blocks
        
def to_stan(rvmap,pro_tips):
    stan_codes = []
    for tip in pro_tips:
        tip_type = tip[0]
        if tip_type == 'STAN_NUTS':
            params = tip[1]
            data = tip[2]
            defs = []
            types = {}
            for rv in params + data:
                deff = rvmap[rv].dist.stan_sample()
                typ = rvmap[rv].dist.stan_type()
                defs.append(rvmap[rv].name + ' ~ ' + deff + ' ;')
                types[rv] = typ

            stan_model_block = lambda s: 'model {\n' + s + '\n}'
            stan_model_defs = '\n'.join(defs)
            stan_model = stan_model_block(stan_model_defs)

            stan_param_block = lambda s: 'parameters {\n' + s + ';\n}'
            stan_param_defs = map(lambda x: types[x] + x,params)
            stan_param_defs = ';\n'.join(stan_param_defs)
            stan_parameters = stan_param_block(stan_param_defs)
            
            stan_data_block = lambda s: 'data {\n' + s + ';\n}'
            stan_data_defs = map(lambda x: types[x] + x,data)
            stan_data_defs = ';\n'.join(stan_data_defs)
            stan_data = stan_data_block(stan_data_defs)

            stan_codes.append(stan_data + stan_parameters + stan_model)

    return stan_codes
 

