from relax.vm import *
from relax.primitives import *

def signature(model,const):
    (rvmap,_) = concolic_vm(model('_',const),0)
    rands = 0
    rvs = {}
    output_types = []
    for rv in rvmap:
        (rand,output_type) = rvmap[rv].dist.lean_type()
        rvs[rvmap[rv].name] = (rvmap[rv].dist,list(range(rands,rands+rand)),output_type)
        rands += rand
        output_types.append(output_type)
    return (rvs,rands,output_types)

def translate(model,const):
    (rvs,rands,otypes) = signature(model,const)

    in_type = ' × '.join(rands * ['nnreal'])
    ret_type = ' × '.join(otypes)
    print('noncomputable')
    print('def', model.__name__ + '_code ( u:', in_type ,') :', ret_type,':=')  
    
    for rv in rvs:
        (dist,rbits,_) = rvs[rv]
        print('let ' + rv + ' := ' + dist.lean_sample(rbits) + ' in')

    print('(', ','.join(rvs), ')')

    gen_measurability_proof(model,const)

def gen_access(i,tab):
    if i == 0:
        print(tab + 'apply measurable_fst,')
    elif i == 1:
        print(tab + 'apply measurable_snd,')
    else:
        print(tab + 'apply measurable_snd,')
        gen_access(i-1,tab)
        
    
def gen_arg(arg,rvmap,rands,tab):
    if type(arg) == int:
        # For now, this is a random bit access
        #gen_access(arg,tab)
        if arg == 0:
            print(tab + 'apply measurable_fst,')
        elif arg == rands - 1:
            pass
        else:
            print(tab + 'apply measurable_fst,')
        for i in range(0,arg):
            print(tab + 'apply measurable_snd,')
        print(tab + 'apply measurable_id,')
    elif arg in rvmap:
        # We're dealing with a distribution
        gen_dist(arg,rvmap,rands,tab)
    else:
        print(tab + 'apply measurable_const,')
    
def gen_args(arg,args,rvmap,rands,tab):
    if len(args) == 0:
        gen_arg(arg,rvmap,rands,tab)
    else:
        print(tab + 'apply measurable.prod; simp,')
        print(tab + '{')
        gen_arg(arg,rvmap,rands,tab + '\t')
        print(tab + '},')
        print(tab + '{')
        gen_args(args[0],args[1:],rvmap,rands,tab + '\t')
        print(tab + '},')
    
def gen_dist(rv,rvmap,rands,tab):
    (dist,rbits,_) = rvmap[rv]
    args = dist.args + rbits
    if type(dist) == Uniform:
        print(tab + 'apply measurable.comp,')
        print(tab + 'apply uniform_measurable,')
        gen_args(args[0],args[1:],rvmap,rands,tab)
    elif type(dist) == Binomial:
        print(tab + 'apply measurable.comp,')
        print(tab + 'apply binomial_measurable,')
        # Second argument incorrect because of current simplifcation for binomial
        gen_args(args[1],args[2:],rvmap,rands,tab)
    else:
        print('Not implemented yet: ',dist)

def gen_prod(current_rv,rvlist,rvmap,rands,tab):
    if len(rvlist) == 0:
        gen_dist(current_rv,rvmap,rands,tab)
    else:
        print(tab + 'apply measurable.prod; simp,')
        print(tab + '{')
        gen_dist(current_rv,rvmap,rands,tab + '\t')
        print(tab + '},')
        print(tab + '{')
        gen_prod(rvlist[0],rvlist[1:],rvmap,rands,tab + '\t')
        print(tab + '},')
        
def gen_measurability_proof(model,const):
    (rvs,rands,otypes) = signature(model,const)

    print('\nProof:\n')

    input_types = ['nnreal'] * rands
    print('lemma ' + model.__name__ + '_code' + '_is_measurable: ' + 'measurable ( λ ( u: ' + ' × '.join(input_types) + '),' + model.__name__ + '_code u) := ')
    
    print('begin')
    print('\t' + 'unfold ' + model.__name__ + '_code,')
    
    # The program must return at least one variable

    rvlist = list(rvs.keys())
    gen_prod(rvlist[0],rvlist[1:],rvs,rands,'\t')

    print('end')
