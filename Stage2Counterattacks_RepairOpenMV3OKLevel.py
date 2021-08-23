#import matplotlib.pyplot as plt
from typing import Optional
from functools import partial
from itertools import product
from time import perf_counter
from Stage3Counterattacks import L3min, L3max, T3, Stage3, highlevelY
import csv
import logging

logging.basicConfig(filename='T2T3repaired_openMV3OKLevel.log', filemode='w', level=logging.DEBUG)
logging.getLogger().addHandler(logging.StreamHandler())

#The model given by John minimises delays between components...
#------------------GLOBAL VARIABLES----------------------------
labels={}
#Transformations={}
#Attacks={}
Ranges={}
theData={}
Setters={}
#------------------THIS CPS's CONSTANTS----------------------------
#Physical states of the valve. These are abstract, but it's ok
valve_closed='closed' #OFF
valve_open='open' #ON
valve_opening='opening' #Tup
valve_closing='closing' #Tdown
on='on'
off='off'
ValveStates=[valve_closed,valve_opening,valve_open,valve_closing]
PumpStates=[off,on]
#Modes in the controller.
#Cheating a bit to avoid defining unnecessary equalities...
#if P3 is always on and without attackers
#values are approximated by a linear regression.
#by second
# FL3={\
#     closed:-0.15,\
#     valve_open:0.16,\
#     closing:0.11,\
#     opening:0.11,\
#     }
L2min=800 #in liters
L2max=1000 #in liters
T2=7 #in seconds


#Let us conceptually create the components of the system:
QTimer='Q[timer]'
QP2='Q[P2]'
QMV2='Q[MV2]'
QP3='Q[P3]'
QMV3='Q[MV3]'
QL3='Q[L3]'
YL2='Y[L2]'
YL3='Y[L3]'
BL3='B[L3]'
UMV2='U[MV2]'
OP2='O[P2]'
OMV2='O[MV2]'
#Valve, tank and pump are outside this study.
#This is the set of components that the attacker can interact with at some level.

#-----------------Artificial ranges for the components-------------
#Interesting values for the const functions
QTimerRange={0,7}#range(8)
YL2Range={500, 900, 1100}#{0,799,900,1001,1200}#{0,799,801,999,1001,1200}#
YL3Range={500, 900, 1100}
BL3Range={500, 900, 1100}
OP2Range={on, off}
#State Partition has 3 cases, there are (id+4)^3+(id+2)^3+(id+5)^3 attacks

#Dictionary to access ranges with components
Ranges[QMV2]=ValveStates
Ranges[QMV3]=ValveStates
Ranges[QP2]=PumpStates 
Ranges[QP3]=PumpStates 
Ranges[OP2]=PumpStates 
Ranges[QTimer]=QTimerRange
Ranges[YL2]=YL2Range
Ranges[YL3]=YL3Range
Ranges[BL3]=BL3Range

#Components as defined in the paper for CPSs
#Signal coming from the controller of Stage 3
class A:
    def __init__(self,L3,MV3):
        self.L3=L3
        self.MV3=MV3

#Digital and analog signals
class I: 
    def __init__(self,L2):
        self.L2=L2

class U: 
    def __init__(self,MV2,P2):
        self.MV2=MV2
        self.P2=P2

#Physical channel to P3
class W:
    def __init__(self,P2):
        self.P2=P2

#These model the vectors, whose components are their fields.
class Q:
    def __init__(self):
        self.timer=0 #a timer that can be reset when changing modes
        self.P2=on
        self.MV2=valve_open
    #delta q i a though no a because we are a single CPS
    def delta(self,i:I,a:A):
        timer=self.timer
        P2=self.P2
        MV2=self.MV2
        MV3=a.MV3
        L2=i.L2
        L3=a.L3
        AreDefined=(MV3!=None) and (L3!=None)
        HighLevelStage3= AreDefined and ((L3>=L3max or (MV3 in {valve_closed,valve_closing})))
        LowLevelStage3=AreDefined and ((L3<=L3min or (MV3 in {valve_open,valve_opening})))
        #Default values for the next values
        MV2_= MV2
        P2_ = P2
        timer_=timer+1 
        #Change of state. Transitions are of the form l2i -> l2j
        if  MV2==valve_closed and P2==off: #l21
            if LowLevelStage3 and L2<=L2min:
                MV2_= valve_opening #l27
                P2_ = on
                timer_=0
            elif LowLevelStage3:
                MV2_= valve_closed #l26
                P2_ = on
                #timer_=timer #i=1, j=6
            elif L2<=L2min: 
                MV2_ = valve_opening #l22
                P2_ = off
                timer_=0
            else:
                pass #nothing happens
        elif MV2==valve_opening and P2 == off: #l22
            if LowLevelStage3 and timer >=T2: 
                MV2_= valve_open #l24
                P2_ = on
                #timer_= 0
            elif LowLevelStage3:
                MV2_ = valve_opening #l27
                P2_= on
                #timer_ = timer #Why reset timer? John's model for i=2, j=7
            elif timer >= T2:
                MV2_ = valve_open #l23
                P2_= off
                #timer_ = 0 #i=2,j=3
            else:
                pass
        elif MV2==valve_open and P2 == off: #l23
            if LowLevelStage3 and L2>=L2max: 
                MV2_= valve_closing #l28 
                P2_ = on
                timer_= 0
            elif LowLevelStage3:
                MV2_ = valve_open #l24
                P2_= on 
                #timer_ = timer #i=3, j=4
            elif L2>=L2max:
                MV2_ = valve_closing #l25
                P2_= off
                timer_ = 0 #i=3,j=5
            else:
                pass
        elif MV2==valve_open and P2 == on: #l24
            if HighLevelStage3 and L2>=L2max: 
                MV2_=valve_closing  #l25
                P2_ = off
                timer_= 0
            elif HighLevelStage3:
                MV2_ = valve_open #l23
                P2_= off
                #timer_ = timer#i=4, j=3
            elif L2>=L2max:
                MV2_ = valve_closing #l28
                P2_= on
                timer_ = 0 #i=4,j=8
            else:
                pass
        elif MV2==valve_closing and P2==off: #l25
            if LowLevelStage3 and timer>=T2:
                MV2_= valve_closed  #l26
                P2_ = on
                #timer_= 0 #i=5, j=6
            elif LowLevelStage3:
                MV2_ = valve_closing #l28
                P2_= on
                #timer_ = timer #i=5, j=8
            elif timer>=T2:
                MV2_ = valve_closed #l21
                P2_= off
                #timer_ = 0 #i=5,j=1
            else:
                pass
        elif MV2==valve_closed and P2 == on: #l26
            if HighLevelStage3 and L2<=L2min: 
                MV2_=valve_opening  #l22
                P2_ = off
                timer_= 0 #i=6, j=2
            elif HighLevelStage3:
                MV2_ = valve_closed #l21
                P2_= off
                #timer_ = timer#i=6, j=1
            elif L2<=L2min:
                MV2_ = valve_opening #l27
                P2_= on
                timer_ = 0 #i=6,j=7
            else:
                pass
        elif MV2==valve_opening and P2 == on: #l27
            if HighLevelStage3 and timer>=T2: 
                MV2_=valve_open  #l23
                P2_ = off
                #timer_= 0 #i=7, j=3
            elif HighLevelStage3:
                MV2_ = valve_opening #l22
                P2_= off
                #timer_ = timer#i=7, j=2
            elif timer>=T2:
                MV2_ = valve_open #l24
                P2_= on
                #timer_ = 0 #i=7,j=4
            else:
                pass
        elif MV2==valve_closing and P2 == on: #l28
            if HighLevelStage3 and timer>=T2: 
                MV2_=valve_closed  #l21
                P2_ = off
                #timer_= 0 #i=8, j=1
            elif HighLevelStage3:
                MV2_ = valve_closing #l25
                P2_= off
                #timer_ = timer#i=8, j=5
            elif timer>=T2:
                MV2_ = valve_closed #l26
                P2_= on
                #timer_ = 0 #i=8,j=6
            else:
                pass
        else:
            pass
        #update values
        self.MV2=MV2_
        self.L2=L2
        self.P2=P2_
        self.timer=timer_
        return self

    def theta(self):
        return O(self.MV2,self.P2)
    
    # Stage 2 has no Beta function
    # def beta(self):
    #     return B(self.L3, self.MV3)

class X:
    def __init__(self):
        #Physical state
        self.L2=990
        self.MV2=valve_open#closed 
        self.P2=on

    #delta x u v
    def delta(self,u:U): 
        MV2=self.MV2
        P2=self.P2
        Inflow=None
        Outflow=None
        #Inflow
        if MV2==valve_open:
            Inflow=0.46
        elif MV2==valve_closed:
            Inflow=0
        else:
            Inflow=0.23
        #Outflow
        if P2==on:
            Outflow=0.31
        else:
            Outflow=0
        L2_=min(1200,max(0, self.L2+Inflow-Outflow))
        #Update
        self.L2=L2_
        self.MV2=u.MV2 #This is responding to the actuator. Note that under this model you can, in one step, change the valve from being opening to being it to be closed. Maybe it is ok, I'll check with John
        self.P2=u.P2
        return self

    #theta 
    def theta(self):
        return Y(self.L2)
    #theta 
    def beta(self):
        return W(self.P2)

#Sensor
class Y: 
    def __init__(self,L2):
        self.L2=L2
    def theta(self):
        return I(self.L2)

#Actuator
class O: 
    def __init__(self,MV2,P2):
        self.MV2=MV2
        self.P2=P2

    def theta(self):
        return U(self.MV2,self.P2)

#The state of our CPS
class Stage2:
    def __init__(self,deformation):        
        self.time=0 #in seconds
        self.x=X()
        self.q=Q()
        self.a=A(None,None)
        #self.v=(valve_open,on)
        self.y=self.x.theta()
        self.i=self.y.theta()
        self.o=self.q.theta()
        # self.b=self.q.beta()
        self.u=self.o.theta()
        self.w=self.x.beta() 
        self.deformation=deformation

    #There are two ways to apply attacks: one is in the global state of the CPS, or the other is in the component of Stage3, which is why we allow attacks here. If you apply the attack globally, pass id to this function so you don't keep transforming it.
    def step(self,attack,a:A):
        if self.deformation != None:
            self=self.deformation.apply(self) #attack
        if attack != None:    
            self=attack.apply(self) #counterattack.
        #The model John has is a zero-delay model between process and controller.
        #we first get the current values
        #collect the new values for y,i,o,u
        y_=self.x.theta() #ugh we keep generating them, 
        i_=self.y.theta()
        o_=self.q.theta()
        w_=self.x.beta()
        u_=self.o.theta()
        #update x, q and the rest
        self.x.delta(self.u)
        self.q.delta(self.i,a)#(il3)
        self.y=y_
        self.i=i_
        self.o=o_
        self.u=u_
        self.w=w_
        # self.b=b_ 
        #update the observations.

        return self
    
    # def setComponent(self,component,transformation):
    #     #This is a big switch
    #     if component==QMV2 :
    #         self.q.MV2=transformation(self.q.MV2)
    #     elif component==QP2 :
    #         self.q.P2=transformation(self.q.P2)
    #     elif component== YL2 :
    #         self.y.L2=transformation(self.y.L2)
    #     elif component== UMV2 :
    #         self.u.MV2=transformation(self.u.MV2)
    #     else:
    #         logging.info("Unknown component: "+str((component,transformation)))
    #         quit()
    #     return self

class CPSState:
    def __init__(self,Stage2,Stage3,deformation,repair):
        self.Stage2=Stage2
        self.Stage3=Stage3
        self.deformation = deformation
        self.repair = repair
        self.time =0

    #def step(self,attackStage2,attackStage3):
    def step(self,attack):
        self.time = self.time+1
        if self.repair !=None:
            self.repair.apply(self)
        #I thought I wanted product attacks but if we are having visibility in stage 2 and effects on stage 3, then we maybe we should not do it isolated.
        if self.deformation !=None:
            self.deformation.apply(self)
        if attack != None:
            attack.apply(self) #We are going to apply the attack by components, so you'd better define attack as a product function.
        # if (attack!=id and self.stage2.time> 1600):
        #     logging.info(self.stage2.time, self.stage2.x.L2,self.stage2.q.mode,self.stage2.a.L3, self.stage2.a.MV3)
        a2=self.Stage3.b #Get the 
        v3=self.Stage2.w
        #v2_=stage3.w3
        self.Stage2.step(None,a2) 
        self.Stage3.step(None,v3)
        # if self.time % 1000 ==0 :
        #     logging.info((self.Stage2.x.P2, self.Stage2.x.MV2, self.Stage2.x.L2,self.Stage3.x.L3, self.Stage3.x.MV3))
        return self

    def setComponent(self,component,transformation):
        #This is a big switch
        if component==QMV2 :
            self.Stage2.q.MV2=transformation(self.Stage2.q.MV2)
        elif component==QP2 :
            self.Stage2.q.P2=transformation(self.Stage2.q.P2)
        elif component==QMV3 :
            self.Stage3.q.MV3=transformation(self.Stage3.q.MV3)
        elif component==QP3 :
            self.Stage3.q.P3=transformation(self.Stage3.q.P3)
        elif component== YL2 :
            self.Stage2.y.L2=transformation(self.Stage2.y.L2)
        elif component== UMV2 :
            self.Stage2.u.MV2=transformation(self.Stage2.u.MV2)
        elif component== YL3 :
            self.Stage3.y.L3=transformation(self.Stage3.y.L3)
        elif component== BL3 :
            self.Stage3.b.L3=transformation(self.Stage3.b.L3)
        elif component==OP2 :
            self.Stage2.o.P2=transformation(self.Stage2.o.P2)
        elif component==OMV2 :
            self.Stage2.o.MV2=transformation(self.Stage2.o.MV2)
        else:
            logging.info("Unknown component: "+str((component,transformation)))
            quit()
        return self

    def iSteps(self,s:int,attack):
        for _ in range(s):
            self.step(attack)
        return self

    # def old_collectDataUntil(self,s,attack,delta,getters,stopCond):
    #     #this method returns a dictionary whose keys are the getters, and whose values are a pair of (domain,codomain)'
    #     theCodomains={}
    #     theDomain=[]
    #     SuccessfulAttacks=set()
    #     for g in getters:
    #         theCodomains[g]=[] #empty codomain for now.
    #     for i in range(s):
    #         if i%delta==0:
    #             theDomain.append(i)
    #             for g in getters:
    #                 theCodomains[g].append(g(self)) #attach data to the respective codomain
    #         anyStopCond=False
    #         for stopCond in stopConds:
    #             if stopCond(self):
    #                 #logging.info('stop condition '+labels[stopCond]+' triggered at time '+str(i)+' for attack '+(labels[attack])+' at mode '+str(self.stage2.q.mode))
    #                 logging.info('stop condition '+labels[stopCond]+' triggered at time '+str(i)+' for attack '+(labels[attack]))
    #                 SuccessfulAttacks.add((attack,stopCond,i))
    #                 anyStopCond=True
    #                 break
    #             else:
    #                 self.step(attack) #This is where the magic happens
    #         if anyStopCond:
    #             break
    #     #pair with the domain
    #     for g in getters:
    #         theCodomains[g]=(theDomain,theCodomains[g])
    #     return (theCodomains,SuccessfulAttacks)

#GETTERS
def getXL3(s:CPSState):
    return s.Stage3.x.L3
labels[getXL3]='x[L3]'

def getXL2(s:CPSState):
    return s.Stage2.x.L2
labels[getXL2]='x[L2]'

def getYL3(s:CPSState):
    return s.Stage3.y.L3
labels[getYL3]='y[L3]'

def getMode(s:CPSState):
    return s.Stage3.q.mode
labels[getMode]='getMode'

#Stopping conditions
def timeEnds(s:CPSState):
    return False
labels[timeEnds]='timeout'

def tankT2NeverOverflows(s:CPSState):
    return not s.Stage2.x.L2>=1200
labels[tankT2NeverOverflows]='Tank T2 Never Overflows'

def tankT2NeverEmpties(s:CPSState):
    return not s.Stage2.x.L2<=0
labels[tankT2NeverEmpties]='Tank T2 Never Empty'

def tankT3NeverOverflows(s:CPSState):
    return not s.Stage3.x.L3>=1200
labels[tankT3NeverOverflows]='Tank T3 Never Overflows'

def tankT3NeverEmpties(s:CPSState):
    return not s.Stage3.x.L3<=0
labels[tankT3NeverEmpties]='Tank T3 Never Empty'

#we can use partial functions to define attacks! I will create a class for them though   

class Predicate:
    def __init__(self,function,semantics):
        self.function=function
        self.semantics=semantics

    def __repr__(self):
        return str(self)

    def __str__(self):
        return self.semantics
    
    def evaluate(self,s:CPSState):
        return self.function(s)

    # def __eq__(self, other):
    #     if isinstance(other, self.__class__):
    #         return self.function == other.function

class Transformation:
    component=None
    function=None

    def __init__(self,function,component,value):
        self.component=component
        self.function=function
        self.value=value

    def __repr__(self):
        return str(self)

    def __str__(self):
        if self.function==id:
            return 'id('+str(self.component)+')'
        else:
            return '('+str(self.component)+'->'+str(self.value)+')'

    def apply(self,s:CPSState):
        if self.component!=None:
            s=s.setComponent(self.component,self.function)
        else:
            s=self.function(s)
        return s
    
    # def __eq__(self, other):
    #     if isinstance(other, self.__class__):
    #         return self.component == other.component and self.function==other.function and self.value == other.value

class Attack:
    Components=None
    Basis=None
    Formula = None#Type {component->{base->Value}}
    Representation=None

    def __init__(self,Components,Basis,Formula):
        self.Components=Components
        self.Basis=Basis
        self.Formula=Formula
        self.computeRepresentation()
    
    def computeRepresentation(self):
        res={}
        for b in self.Basis:
            res[b]={}
        for c in self.Components:
            for b in self.Basis:
                #str_c = str(c)+'->'+str((self.Formula[c])[b])
                str_c = str((self.Formula[c])[b])
                res[b][c]=str_c
        self.Representation=""
        for b in self.Basis:
            str_b='('+str(b)+')=>['
            for c in self.Components:
                str_b+=res[b][c]+', '
            str_b=str_b[:-2]
            self.Representation+=str_b+'] + '
        self.Representation=self.Representation[:-3]
        return self
        
    def changeFormula(self,component,basis,transformation):
        self.Formula[component][basis]=transformation
        self.computeRepresentation()
        return self
        
    def apply(self,s:CPSState):    
        for c in self.Components:
            for b in self.Basis:
                if b.evaluate(s):
                    t = self.Formula[c][b]
                    s=t.apply(s)
        return s

    def __repr__(self):
        return str(self)

    def __str__(self):
        return self.Representation 
    
#     def __eq__(self, other):
#         if isinstance(other, self.__class__):
#             return self.Representation == other.Representation
    
#     def __hash__(self):
#         return hash(str(self))
# #
#The attacker model should have a way to count. This is a vector space, but it is ordered due to its combinatorial nature
    #Functionality I want: to give a set of components and this acts as a generator that I can keep asking "gimme next attack".
class AttackerModel:
    #Each attacker model is 
    #It has a set of representative transformations, one for each component to be attacked
    Basis=None #Type is [Stage3->Bool]
    VulnerableComponents=None #Type is set(component)
    Transformations=None #Type is {component-> (id:[const v])} 
    CurrentTargets=None #Type is Set(component)
    CurrentAttack=None #Type is ((Set(component),Set(predicates)),{component->{predicate->const_v}})
    LastGeneratorState=None #Type is ((Set(component),Set(predicates)),{component->{predicate->const_v}}).
    Modulo=None #Type is: {component->int}. helps us count.
    GeneratorState= None #This is an internal state to generate the next attack with minimal effort. This probably is a tuple of indices 
    #It at least has {CurrentTargets->Index} where I can use the index to go go transformations[c][i] and obtain the last used transformation.
    #Assume these Transformations do NOT contain the identity function. These are the Gamma and the basis.
    #Gamma: Type is {component-> Set(const v)} 
    #Pies: Type is set(Stage3->Bool)
    def __init__(self,Gamma,Pies):
        #
        self.Transformations={}
        self.Modulo={}
        self.Basis=list(Pies)
        self.VulnerableComponents=Gamma.keys()
        size=1
        for c in self.VulnerableComponents:
            Identity_c=Transformation(id,c,None)
            Delta_c=list(Gamma[c]) #Type is Set(const v)
            Transformations_c=[Identity_c] #Start with the identity
            Transformations_c.extend(Delta_c) #Add the rest of the options
            modulo_c=len(Transformations_c) #Compute the last index so it ranges from 0 to maxIndex-1
            size*=modulo_c
            self.Modulo[c]=modulo_c #This works. n transformations returns modulo n+1, so indices range from 0 to n
            self.Transformations[c]= Transformations_c
        self.resetGenerationParameters()
        self.size=(size)**len(self.Basis)

    # def __repr__(self):
    #     return "Test()"

    # def __str__(self):
    #     return "member of Test"
    #(CurrentTargets,LastAttack) together 

    #I give a set of components because of monotonicity. The m
    #components: the target components: Type is set(component)
    def setGenerationParameters(self,Components):
        self.resetGenerationParameters()
        self.CurrentTargets=Components
        return self
    
    def nextAttack(self):
        #This method generates 
        if self.GeneratorState == self.LastGeneratorState:#self.CurrentAttack == self.LastAttack:
            return None #There are no more attacks
        if self.CurrentAttack == None:
            #Generate the first attack
            NextAttack_Formula={}
            for c in self.VulnerableComponents:
                Formula_c={}
                #Get the first transformation for this component (should be id)
                NextTransformation_c=self.Transformations[c][0]
                #put this value in all values of the basis
                for b in self.Basis:
                    Formula_c[b]=NextTransformation_c
                NextAttack_Formula[c]=Formula_c
            NextAttack=Attack(self.VulnerableComponents,self.Basis,NextAttack_Formula)
            self.CurrentAttack=NextAttack
            return self.CurrentAttack
        else:
            #Example: Current attack is of the form (k_1.k_2.k_3)pi_1+(k'_1.k'_2.k'_3)pi_2+...
            #add one to the current attack. 
            #Next attack should be((k_1+1).k_2.k_3)pi_1+(k'_1.k'_2.k'_3)pi_2+...
            #However, k_1 may be at a max, in such case we need
            #Next attack should be((id.(k_2+1).k_3)pi_1+(k'_1.k'_2.k'_3)pi_2+...
            #This process repeats. If you run out of options in p_1, move to pi_2
            for b in self.Basis: #Break once you found the next element.
                #getCurrentIndex for Currentbasis
                t_b=self.GeneratorState[b] #Type is {component->int}
                for c in self.VulnerableComponents:
                    c_i=t_b[c] #
                    c_i_=(c_i+1)%self.Modulo[c] #The next index 
                    if c_i_ !=0:
                        #awesome! We found the next attack!
                        #Now, we need to create the next attack. But we can do by applying the changes directly to the Current attack.
                        #use your current indices to focus on the current attack
                        self.GeneratorState[b][c]=c_i_
                        self.CurrentAttack.changeFormula(c,b,self.Transformations[c][c_i_])
                        #self.CurrentAttack.Formula[c][b]=self.Transformations[c][c_i_]
                        #This is why I like vectorial programming. You get lenses for free.
                        return self.CurrentAttack
                    else:
                        self.GeneratorState[b][c]=c_i_
                        self.CurrentAttack.changeFormula(c,b,self.Transformations[c][c_i_])
                        #self.CurrentAttack.Formula[c][b]=self.Transformations[c][c_i_] #put this at zero.
            return None #To avoid reaching this point, we stored the Last Attack.

    #This method helps me reset the GeneratorState
    def resetGenerationParameters(self):
        self.LastAttack={}
        self.CurrentAttack=None
        #BasisIndices=[] #The basis indices are always the same lol
        # for _ in self.Basis:
        #     BasisIndices.append(0)
        #Each basis acts on a set of components, and each component has an associated transformation. 
        ComponentIndices={}
        for b in self.Basis:
            ComponentIndices[b]={}
            for c in self.VulnerableComponents:
                ComponentIndices[b][c]=0
        #Compute the last attack of type ((Set(component),Set(predicates)),{component->{predicate->const_v}})
        #Just touch all of them. We can think of a reduction function later
        self.LastGeneratorState={} #self.LastGeneratorState[b][c]=LastIndex_c
        for b in self.Basis:
            self.LastGeneratorState[b]={}
            for c in self.VulnerableComponents:
                LastIndex_c=self.Modulo[c]-1
                self.LastGeneratorState[b][c]=LastIndex_c
            #There is no need to compose the transformations. The CPS will apply each transformation by looking at the set of components.
        self.CurrentTargets=None
        self.GeneratorState=ComponentIndices#,BasisIndices)       
        return self

#def setQMode(predicate,transformation,s:CPSState):
def setQMV2(predToTrans,s:CPSState):
    for k in predToTrans.keys():
        if k(s):
            s.Stage2.q.MV2=predToTrans[k](s.Stage2.q.MV2)
            break        
    return s
labels[setQMV2]='Q[MV2]='
Setters[QMV2]=setQMV2

def setQTimer(predToTrans,s:CPSState):
    for k in predToTrans.keys():
        if k(s):
            s.q.timer=predToTrans[k](s.q.timer)
            break        
    return s

labels[setQTimer]='Q[timer]='
Setters[QTimer]=setQTimer

def setYL3(predToTrans,s:CPSState):
    for k in predToTrans.keys():
        if k(s):
            s.y.L3=predToTrans[k](s.y.L3)
            break        
    return s
Setters[YL3]=setYL3
labels[setYL3]='Y[L3]='

#This is a very interesting attack because it takes the state into account
def resetTimer(s:CPSState):
    s.q.timer=0
    return s
labels[resetTimer]='ResetTimer'

def forceClosedMode(s:CPSState):
    s.q.mode='closed'
    return s
labels[forceClosedMode]='forceClosedMode'

def forcevalve_openMode(s:CPSState):
    s.q.mode='valve_open'
    return s
labels[forcevalve_openMode]='forcevalve_openMode'

#COUNTERATTACK TRANSFORMATIONS
#(Y[L3]>L3max)=>[(Q[MV3]->open), id(Q[P3])] + (Y[L3]<L3min)=>[id(Q[MV3]), id(Q[P3])] + (L3min<=Y[L3]<=L3max)=>[id(Q[MV3]), id(Q[P3])]
#Attacks do nothing when Y[L3]>L3max
def openMV3IfGoodLevelT3(s:CPSState):
    if goodT3level(s): #The problem with this line is that it does not distinguish normal executions from exceptional ones.
        #if highT3levelY(s):
            s.Stage3.q.MV3=open  #counter attack common action
    return s
labels[openMV3IfGoodLevelT3]='openMV3IfGoodLevelT3'

#Attack to counter: (x[L3]<L3min)=>[(O[P2]->off), id(O[MV2])] + (L3min<=x[L3]<=L3max)=>[id(O[P2]), id(O[MV2])] + (x[L3]>L3max)=>[id(O[P2]), id(O[MV2])]
#Generic transformations
#Generic transformations

def id(s):
    return s
    
labels[id]='id'
 

def const(v,x):
    return v
labels[const]='const'

def addition(v,x):
    return x+v
labels[addition]='addition'

def prettyPrint(d):
    res=''
    for k in d.keys():
        res+='('+labels[k]+')=>'+labels[d[k]]+', '
    return res


#PREDICATES. 
def all(s:CPSState):
    return True
labels[all]='True'

def lowT2level(s:CPSState):
    return (s.Stage2.x.L2<=L2min)
labels[lowT2level]='x[L2]<L2min'

def highT2level(s:CPSState):
    return (s.Stage2.x.L2>=L2max)
labels[highT2level]='x[L2]>L2max'

def lowT3level(s:CPSState):
    return (s.Stage3.x.L3<=L3min)
labels[lowT3level]='x[L3]<L3min'

def highT3level(s:CPSState):
    return (s.Stage3.x.L3>=L3max)
labels[highT3level]='x[L3]>L3max'

def goodT2level(s:CPSState):
    return (not lowT2level(s)) and (not highT2level(s))
labels[goodT2level]='L2min<=x[L2]<=L2max'

def goodT3level(s:CPSState):
    return (not lowT3level(s)) and (not highT3level(s))
labels[goodT3level]='L3min<=x[L3]<=L3max'

# def badlevel(s:CPSState):
#     return (lowlevel(s)) or (highlevel(s))

# def notlowlevel(s:CPSState):
#     return not lowlevel(s)
# labels[notlowlevel]='L3>=L3min'

def lowT2levelY(s:CPSState):
    return (s.Stage2.y.L2<L2min)
labels[lowT2levelY]='Y[L2]<L2min'

def highT2levelY(s:CPSState):
    return (s.Stage2.y.L2>L2max)
labels[highT2levelY]='Y[L2]>L2max'

def goodT2levelY(s:CPSState):
    return (not lowT2levelY(s)) and (not highT2levelY(s))
labels[goodT2levelY]='L2min<=Y[L2]<=L2max'

def lowT3levelY(s:CPSState):
    return (s.Stage3.y.L3<L3min)
labels[lowT3levelY]='Y[L3]<L3min'

def highT3levelY(s:CPSState):
    return (s.Stage3.y.L3>L3max)
labels[highT3levelY]='Y[L3]>L3max'

def goodT3levelY(s:CPSState):
    return (not lowT3levelY(s)) and (not highT3levelY(s))
labels[goodT3levelY]='L3min<=Y[L3]<=L3max'

#Now, we have partition of the states. Let us do some math.
#  2 state classes and there are 5 transformations for the mode. This alone yields 5^2=25 attacks for the attacker that controls the mode of the controller. Bigger partitions increase the size of the problem exponentially.

#COMPONENT TRANSFORMATIONS
#These functions are the transformations of values of setQMode.
#modesTransformations=[identity]+list(map (lambda v: partial(const,v), modesRange))
#I'll do it as a for, because I also want to generate nice labels. I dunno if python can handle (mt,lbls)=map(\m->(p,lbl[p]) ms), but probably not because I have to wrap list(..) on the right


styles={0:'-',1:'--', 2:':', 3:','}

#Methods which use global variables
def toConstValues(RepresentativeValuesMapping):
    Transformations={}
    print("Generating transformations", end="")
    for c in RepresentativeValuesMapping.keys():
        Transformations_c=[]#[Transformation(id,c,None)] WARNING: id is not a const function
        Range_c=RepresentativeValuesMapping[c]
        for m in Range_c:
            pm = Transformation(partial(const,m),c,m)
            #pm = partial(addition,m)
            #labels[pm]= 'const '+str(m)
            labels[pm]=str(m)+')'
            Transformations_c+=[pm]
        Transformations[c]=Transformations_c
        print('', end=".")
    print("Done!")
    return Transformations


#Methods which use global variables
#Deprecated 
def GenerateTransformations(AttackedComponents):
    Transformations={}
    print("Generating transformations", end="")
    for c in AttackedComponents:
        TransformationsForThisComponent=[id]
        for m in Ranges[c]:
            pm = partial(const,m)
            #pm = partial(addition,m)
            #labels[pm]= 'const '+str(m)
            labels[pm]=str(m)+')'
            TransformationsForThisComponent+=[pm]
        Transformations[c]=TransformationsForThisComponent
        print('', end=".")
    print("Done!")
    return Transformations


#Return type of LBA is a tuple with several things. 
#To write to CSV, we need to return list of dictionaries (or a dictionary of dictionaries). That is perfect.
#Each dictionary in the list corresponds to a row in the CSV.
#
def LatentBehaviourAnalysis(Attacker,CounterAttacker,Requirements,TestingTime):
    #LBH has two modes, attacker mode and counterattacker mode
    #We are in counterattacker mode.
    #we can sequentially test attacks using the Attacker model
    Results=set()
    Results_NormalBehaviour=None
    Results_SuccessfulAttackToBehaviour={}
    Results_UnsuccessfulAttackToBehaviour={}
    Results_AttackAndCounterAttackToBehaviour={}
    AttackEnumeration={}
    CounterAttackEnumeration={}
    AttackCounter=0
    repair=Transformation(openMV3IfGoodLevelT3,None,None)
    while True:
        Attack=Attacker.nextAttack()
        if Attack==None:
            #we are done!
            break
        #cps=CPSState(Stage2(None),Stage3(None),Transformation(offP3IfP2OffAndLowlevel,None,None))
        cps=CPSState(Stage2(None),Stage3(None),None,repair)
        AttackCounter+=1
        AttackEnumeration[Attack]=AttackCounter #This could be a list...
        logging.info("------------------------------------------------")
        logging.info("Testing Attack #"+str(AttackCounter))
        (BrokenRequirement,Trace)=TestAttack(cps,Attack,Requirements,TestingTime)
        if AttackCounter==1:
            #We are testing the identity attack. Collect the normal behaviour
            Results_NormalBehaviour=Trace
        if BrokenRequirement==None:
            #Good, this attack did not break any requirement. Get the next attack and try again.
            logging.info('No requirement broken by attack '+str(Attack))
            Results_UnsuccessfulAttackToBehaviour[AttackEnumeration[Attack]]=Trace
            continue
        else:
            #a requirement was broken. create a new CPS using the attack you just discovered
            Results_SuccessfulAttackToBehaviour[AttackEnumeration[Attack]]=Trace
            CounterAttacker.resetGenerationParameters()
            #logging.info("Deformed CPS under "+str(Attack))
            CounterAttackCounter=0
            while True:
                CounterAttack=CounterAttacker.nextAttack()
                if CounterAttack==None:
                    #we are done!
                    break
                CounterAttackCounter+=1
                cps=CPSState(Stage2(None), Stage3(None),Attack,repair)                
                #logging.info("Testing counterattack #"+str(CounterAttackCounter))
                print("Testing counterattack #"+str(CounterAttackCounter), end='\r')
                (BrokenRequirement,CounterTrace)=TestCounterAttack(cps,CounterAttack,Requirements,TestingTime)
                if BrokenRequirement!=None:
                    #Shame, this was not a counterattack. Try again                    
                    continue
                else:
                    #We found a counterattack!
                    logging.info("Found counterattack" + str(CounterAttack))
                    Results.add((str(Attack),str(CounterAttack)))
                    CounterAttackEnumeration[CounterAttack]=CounterAttackCounter
                    Results_AttackAndCounterAttackToBehaviour[(AttackEnumeration[Attack],CounterAttackEnumeration[CounterAttack])]=CounterTrace
                    break
                    #return (Attack,CounterAttack)
            #No counterattack was successful. Report the attack as unfixable under this counterattacker model
            if CounterAttack==None:
                logging.info("Could not find counterattack for "+str(Attack))
                Results.add((str(Attack),None))
    return (Results,AttackEnumeration,CounterAttackEnumeration,Results_NormalBehaviour,Results_UnsuccessfulAttackToBehaviour,Results_SuccessfulAttackToBehaviour, Results_AttackAndCounterAttackToBehaviour)

def TestAttack(s:CPSState,Attack:Attack,Requirements,TestingTime:int):
    BrokenRequirement=None
    Trace={}
    #RequirementsBroken=set() #Set which collects all requirements broken by this 
    for i in range(TestingTime):
        Trace[i]=(getXL2(s),getXL3(s))
        for req in Requirements:
            if not req.evaluate(s): 
                #Attack was successful. 
                logging.info('Requirement "'+str(req)+'" broken at time '+str(i)+' by attack '+str(Attack))
                BrokenRequirement=req
                return (BrokenRequirement,Trace)
        s.step(Attack) #This is where the magic happens
    #pair with the domain
    return (BrokenRequirement,Trace)

def TestCounterAttack(s:CPSState,CounterAttack:Attack,Requirements,TestingTime:int):
    #RequirementsBroken=set() #Set which collects all requirements broken by this 
    getXL3(s)
    Trace={}
    for i in range(TestingTime):
        Trace[i]=(getXL2(s),getXL3(s))
        for req in Requirements:
            if not req.evaluate(s):
                #CounterAttack was unsuccessful.
                return (req,Trace)
        s.step(CounterAttack) #This is where the magic happens
    #pair with the domain
    return (None,Trace)

# def old_LatentBehaviourAnalysis(AttackedComponents,Attacks):
#     SuccessfulAttacks=set()
#     SuccessfulAttackers=set()
#     logging.info("Performing Latent Behaviour Analysis")
#     counter=-1
#     AttackNumber=1
#     CollectedAttacks=0
#     for component in AttackedComponents:
#         logging.info("Started attacking component: "+str(component))
#         for attack in Attacks[component]:
#             logging.info("Attack #"+str(AttackNumber), end='\r')  
#             #logging.info(labels[attack]) #ATTACK GENERATION IS FINE.
#             cps=CPSState()
#             counter=(counter+1)%4
#             if (not CheckAllAttacks) and (component in SuccessfulAttackers):
#                 break  #we already know that this attacker has some attack that is successful.
#             results=cps.collectDataUntil(time,attack,delta,getters,stopConds)
#             AttackNumber+=1
#             theData[attack]=results[0]
#             SuccessfulAttacks_=results[1]
#             if len(SuccessfulAttacks_)>0:
#                 #an attack was successful
#                 SuccessfulAttackers.add(component)
#                 CollectedAttacks+=1
#                 for g in getters:
#                     (d,c)=theData[attack][g]
#                     plt.plot(d,c, styles[counter], label=labels[attack])
#                 SuccessfulAttacks.update(SuccessfulAttacks_)
#             elif DrawUnsuccessful:
#                 CollectedAttacks+=1
#                 for g in getters:
#                     (d,c)=theData[attack][g]
#                     plt.plot(d,c, styles[counter], label=labels[attack])#NO LABELS
#         logging.info("Finished attacking component: "+str(component))
#     return (SuccessfulAttacks,SuccessfulAttackers)
#--------------------------------------------------------------------
#-------------------CONFIG FOR SIMULATION----------------------------
#--------------------------------------------------------------------


# time =1*60*60#seconds --X*60*60 for X hours
# delta = 1
# partition={lowlevel,highlevel,goodlevel}#{all}#{notlowlevel,lowlevel}#{partial(const, True)}#{goodlevel,badlevel}##{goodlevel,badlevel}
# stopConds={tankNeverEmpties, tankNeverOverflows}#,tankT3Overflows]#{timeEnds}#
# getters=[getXL3]#,getXL3]#[getL3]
# theYlabel='Level'
# CheckAllAttacks=True#False#
# EnableAttacks=True#False
# DrawUnsuccessful=False#True#True#False
# DrawOriginal=True#False#
# LabelOriginal=True#False

#AttackEnumeration:{Attack:Int}
#NormalBehaviour:{int:float}
#AttackToBehaviour:{Attack:{int:float}}
#AttackAndCounterAttackToBehaviour:{(Attack,Attack):{int:float}}
def createReport(AttackEnumeration,CounterAttackEnumeration,NormalBehaviour,UnsuccessfulAttackToBehaviour,SuccessfulAttackToBehaviour,AttackAndCounterAttackToBehaviour,TestingTime):
    #Do not give the explicit names 
    with open('Stage2NormalBehaviourRepaired_openMV3OKLevel.csv','w', newline='') as csvfile:
        ResultsWriter = csv.DictWriter(csvfile, fieldnames=list(NormalBehaviour.keys()))
        ResultsWriter.writeheader()
        ResultsWriter.writerow(NormalBehaviour)
    if len(UnsuccessfulAttackToBehaviour.keys())>0:
        with open('Stage2UnsuccessfulAttackBehaviourRepaired_openMV3OKLevel.csv','w', newline='') as csvfile:
            fieldnames=['Attack#']
            fieldnames+=list(range(TestingTime))
            # for k in AttackToBehaviour.keys():
            #     fieldnames+=list(AttackToBehaviour[k].keys())
            ResultsWriter = csv.DictWriter(csvfile, fieldnames=fieldnames)
            ResultsWriter.writeheader()
            for k in UnsuccessfulAttackToBehaviour.keys():
                UnsuccessfulAttackBehaviour=UnsuccessfulAttackToBehaviour[k]
                UnsuccessfulAttackBehaviour['Attack#']=k
                ResultsWriter.writerow(UnsuccessfulAttackBehaviour)
    if len(SuccessfulAttackToBehaviour.keys())>0:
        with open('Stage2SuccessfulAttackBehaviourRepaired_openMV3OKLevel.csv','w', newline='') as csvfile:
            fieldnames=['Attack#']
            fieldnames+=list(range(TestingTime))
            # for k in AttackToBehaviour.keys():
            #     fieldnames+=list(AttackToBehaviour[k].keys())
            ResultsWriter = csv.DictWriter(csvfile, fieldnames=fieldnames)
            ResultsWriter.writeheader()
            for k in SuccessfulAttackToBehaviour.keys():
                SuccessfulAttackBehaviour=SuccessfulAttackToBehaviour[k]
                SuccessfulAttackBehaviour['Attack#']=k
                ResultsWriter.writerow(SuccessfulAttackBehaviour)
        with open('Stage2AttackCounterattackBehaviourRepaired_openMV3OKLevel.csv','w', newline='') as csvfile:
            fieldnames=['Attack#','Counterattack#']
            fieldnames+=list(range(TestingTime))
            # for k in AttackToBehaviour.keys():
            #     fieldnames+=list(AttackToBehaviour[k].keys())
            ResultsWriter = csv.DictWriter(csvfile, fieldnames=fieldnames)
            for k in AttackAndCounterAttackToBehaviour.keys():
                (a,c)=k
                ResultsWriter.writeheader()
                AttackAndCounterAttackBehaviour=AttackAndCounterAttackToBehaviour[(a,c)]
                AttackAndCounterAttackBehaviour['Attack#']=a
                AttackAndCounterAttackBehaviour['Counterattack#']=c
                ResultsWriter.writerow(AttackAndCounterAttackBehaviour)
    # with open('Stage3AttackBehaviour_openMV3OKLevel.csv','w', newline='') as csvfile:
    #     fieldnames=['A']
    #     ResultsWriter = csv.DictWriter(csvfile, fieldnames=fieldnames)
    return 0

#--------------------------------------------------------------------
#-------------------SYSTEMATIC ATTACK GENERATION --------------------
#--------------------------------------------------------------------
def main():
    #CONFIG
    TestingTime=6*60*60#24*60*60
    Requirements=[Predicate(tankT2NeverOverflows, labels[tankT2NeverOverflows]),Predicate(tankT2NeverEmpties,labels[tankT2NeverEmpties]),Predicate(tankT3NeverOverflows, labels[tankT3NeverOverflows]),Predicate(tankT3NeverEmpties,labels[tankT3NeverEmpties])]
    #We define the attacker and counter-attacker models
    AttackerCoefficients=toConstValues({OP2:PumpStates, OMV2:[valve_open,valve_closed]}) 
    #toConstValues({YL2:[500,1100]})#toConstValues({BL3:[400, 1100]})#
    #toConstValues({YL3:[500,1000]})
    #toConstValues({YL3:[500]})
    #AttackerCoefficients=toConstValues({UMV3:[valve_open,closed]})
    AttackerBasis = [Predicate(lowT3level, labels[lowT3level]),Predicate(goodT3level, labels[goodT3level]), Predicate(highT3level, labels[highT3level])]
    #[Predicate(lowT2level, labels[lowT2level]),Predicate(goodT2level, labels[goodT2level]), Predicate(highT2level, labels[highT2level])] #[Predicate(all,'True')]#
    CounterAttackerCoefficients=toConstValues({QMV3:[valve_closed,valve_open], QP3:[on,off]}) #, QP3:[on,off]}) #toConstValues({}) #
    CounterAttackerBasis = set([Predicate(lowT3levelY, labels[lowT3levelY]),Predicate(goodT3levelY, labels[goodT3levelY]), Predicate(highT3levelY, labels[highT3levelY])]) #[Predicate(all,'True')] #
    Attacker= AttackerModel(AttackerCoefficients,AttackerBasis)
    #logging.info("Attacker model has size "+str(Attacker.size))
    logging.info("Attacker model has size "+str(Attacker.size))
    CounterAttacker= AttackerModel(CounterAttackerCoefficients,CounterAttackerBasis)
    logging.info("CounterAttacker model has size "+str(CounterAttacker.size))
    #logging.info("CounterAttacker model has size "+str(CounterAttacker.size))
    #Define the CPS
    (Results,AttackEnumeration,CounterAttackEnumeration,NormalBehaviour,UnsuccessfulAttackToBehaviour,SuccessfulAttackToBehaviour,AttackAndCounterAttackToBehaviour)=LatentBehaviourAnalysis(Attacker,CounterAttacker,Requirements,TestingTime)
    #Results is of type Set((Attack, Maybe CounterAttack))
    AttacksWithoutCounterattack=[]
    #These partition the Results
    CounterattackToAttack={}
    createReport(AttackEnumeration,CounterAttackEnumeration,NormalBehaviour,UnsuccessfulAttackToBehaviour,SuccessfulAttackToBehaviour,AttackAndCounterAttackToBehaviour,TestingTime)
    TotalAttacks=len(Results)
    for (a,c) in Results:
        if c == None:
            AttacksWithoutCounterattack.append(a)
        else:
            if not c in CounterattackToAttack.keys():
                CounterattackToAttack[c]=set()
            # else: 
            #     logging.info(c)
            CounterattackToAttack[c].add(a)
            # if not str(c) in CounterattackToAttack.keys():
            #     CounterattackToAttack[str(c)]=set()
            # # else: 
            # #     logging.info(c)
            # CounterattackToAttack[str(c)].add(a)
    #     logging.info(r)
    logging.info("===========================================================")
    if len(CounterattackToAttack)>0:
        logging.info("These counterattacks counter the following attacks:")
        for c in CounterattackToAttack.keys():
            logging.info("-----------------------------------")
            logging.info(str(c)+" counters the following "+str(len(CounterattackToAttack[c]))+" attacks:")
            for a in CounterattackToAttack[c]:
                logging.info(a)
            logging.info("-----------------------------------")
    if len(AttacksWithoutCounterattack)==0:
        logging.info("The attacker model tested did not produce attacks which cannot be countered with the given counter-attacker model. THIS IS NOT VERIFICATION, unless you know this attacker model has complete coverage.")
    else:
        logging.info("The following "+str(len(AttacksWithoutCounterattack)) +" attacks cannot be countered under the current attacker/counter attacker models. Either extend the counter-attacker model, or redesign your CPS:")
        for a in AttacksWithoutCounterattack:
            logging.info(a)
    logging.info("===========================================================")
    logging.info("The robustness of this system with respect to the given attacker model is: "+str(Attacker.size-TotalAttacks)+"/"+str(Attacker.size))
    logging.info("===========================================================")
    # logging.info("TODO: Behaviour of unsuccessful Attacks")
    # logging.info("TODO: for the different attacker models, return robustness, how many attacks did not have counterattacks, to prove robustness goes down, there are attacks that are non-counterable")

# def old_main():
#     #CONFIG
#     AttackedComponents={YL3}#,QMV3}
#     start = perf_counter()
#     if EnableAttacks:
#         Transformations=GenerateTransformations(AttackedComponents)
#         #Now, each component has its own set of transformations
#         (TotalAttacks,Attacks)=GenerateAttacks(AttackedComponents,Transformations)
#         #DO NOT TOUCH THE FOLLOWING
#         (SuccessfulAttacks,SuccessfulAttackers)=LatentBehaviourAnalysis(AttackedComponents,Attacks)
#         logging.info('There are '+str(len(SuccessfulAttacks))+' successful attacks under state partition '+str(set(map(lambda p:labels[p],partition))))
#         logging.info('Tested '+str(TotalAttacks)+' attacks in total')
#         logging.info('Successful attackers with only one component= '+str(SuccessfulAttackers))
#         logging.info('Future work: 1) Combine unsuccessful attacks in different components to see if you can make them successful. \n 2) Create state machines for the termination conditions, so they are more flexible.')
#     if DrawOriginal:
#         cps=CPSState()
#         results=cps.collectDataUntil(time,id,delta,getters,stopConds)
#         origBehaviour=results[0]
#         for g in getters:
#             (d,c)=origBehaviour[g]
#             if LabelOriginal:
#                 plt.plot(d,c, label='Original Behaviour')#NO LABELS
#             else:
#                 plt.plot(d,c)
#     end = perf_counter()
#     logging.info(f"Analysis finished in {end - start:0.4f} seconds")
#     plt.xlabel('Time (sec)')
#     plt.ylabel(theYlabel)
#     #plt.legend()
#     plt.show()


    
#--------------------------------------------------------------------
#-------------------Testing --------------------
#--------------------------------------------------------------------

def TestAttackerModelGeneration():
    Gamma=toConstValues({YL3:YL3Range}) 
    #Pies=set([Predicate(all, 'True')])
    Pies=set([Predicate(lowT2level, labels[lowT2level]),Predicate(highT2level, labels[highT2level])])
    #So far so good
    testModel= AttackerModel(Gamma,Pies)
    na=testModel.nextAttack()
    while na != None:
        logging.info(str(na))
        na=testModel.nextAttack()
    testModel.resetGenerationParameters()
    na=testModel.nextAttack()
    while na != None:
        logging.info(str(na))
        na=testModel.nextAttack()
    return False
    
def TestAttackerModelReset():
    Gamma=toConstValues({YL3:YL3Range}) 
    Pies=set([Predicate(all, 'True')])
    testModel= AttackerModel(Gamma,Pies)
    logging.info(str(testModel.nextAttack()))
    return False

if __name__ == "__main__":
    #TestAttackerModelGeneration()
    #TestAttackerModelReset()
    main()