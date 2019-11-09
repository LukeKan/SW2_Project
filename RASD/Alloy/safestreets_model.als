--Account Parameters
sig Username{}
sig Password{}
-------------------

--Topic of the Mining request
abstract sig Topic{}
one sig PlateTopic extends Topic{}
one sig MDSTopic extends Topic{}
-----------------------------

--Vehicle parameters
sig Plate{}
sig Model{}
sig Brand{}
--------------------

--Account is the generic signature for every registered entity.
--User, LSA and technicians are the specific istances for each specific person.
abstract sig Account{
    userName: one Username,
    password: one Password
}
sig User extends Account{}
sig LSA extends Account{
    availableTechnicians: set Technician,
    competenceArea: set Street
}

sig IdTechnician{}
--The agenda is the list of the scheduled violations allocated by the boss to the technician.
--Also, every technician has exactly one boss and he can receive scheduled violation only by him
sig Technician extends Account{
    idNumber: one IdTechnician,
    agenda:set ScheduledViolation,
    boss: one LSA
}

--Parameters are generic strings that the miner can specify inside his request
sig Parameter{}

sig MiningRequest{
    topic: one Topic,
    parameters: set Parameter,
    miner: one Account
}

--Result can be either positive or negative.
--Violations is the resulting set of the request.
sig Result{}
sig MiningResponse{
    violations:set Violation,
    request:one MiningRequest,
    result:one Result
}

sig Coordinates{
    x:one Int,
    y:one Int
}

--One location could be placed on the intersection of more than one street
sig Location{
    coordinates: one Coordinates,
    streets: set Street
}
--Viceversa one street can contain more than one location
sig Street{
    locations: set Location
}

sig Date{}
sig IdViolation{}
--Violation is a generic entity defined for the state design pattern.
abstract sig Violation{
    id: IdViolation,
    date: Date,
    address:Location,
    user: User,
    plate: Plate
}
--The scheduler can be a LSA which competence area covers the location of the violation.
sig ScheduledViolation extends Violation{
    scheduler: one LSA,
    allocatedTechnicians: set Technician
}
--By default, violations are instanced as PendingViolations , which are all those violation which has yet to be handled.
sig PendingViolation extends Violation{}
--Solved violations are archived violations which have been already dealt by technicians.
sig SolvedViolation extends Violation{}

sig Vehicle{
    plate:Plate,
    model:Model,
    brand:Brand
}

--SuggestedIntervention can be defined only over a location in which at least one violation occured
sig InterventionCause{}
sig SuggestedIntervention{
    location:one Location,
    reason: one InterventionCause,
}

--There could not be a pair of accounts with the same userName.
fact differentUsernames{
    no disj a1,a2:Account | a1.userName=a2.userName
}

--There could not be a pair of violations with the same violation id.
fact differentViolationIds{
    no disj v1,v2:Violation | v1.id=v2.id
} 

--There could not be a pair of vehicles with the same plate.
fact differentPlates{
    no disj v1,v2:Vehicle | v1.plate=v2.plate
}

--There could not be a pair of technician with the same id number.
fact differentTechnicianIds{
    no disj t1,t2 : Technician | t1.idNumber=t2.idNumber
}

--users can not make mining requests on car plates as only authorities are allowed to perform such queries
fact noUserPlateMining{
    all r:MiningRequest | (some u:User | r.miner=u) implies not r.topic=PlateTopic 
    
}

--Users can not request other users violation in an explicit query
fact noOtherUsersViolation{
    all mr:MiningResponse | all m:mr.violations | mr.request.miner in User implies m.user=mr.request.miner
}

--All the available technician of a LSA must have as boss parameter the LSA himself
fact noDifferentBosses{
    all l:LSA | some t: Technician| t in l.availableTechnicians iff t.boss=l
}

--Only the technicians' own boss can schedule them for a violation
fact ownBossScheduling{
    all sv:ScheduledViolation | some t:Technician | t in sv.allocatedTechnicians iff t.boss=sv.scheduler
}

--At most 5 different technicians can be allocated to the same scheduled violation
fact noMorethanFiveTechnPerViolation{
    all v:ScheduledViolation | #(v.allocatedTechnicians)<6
}

--This function returns a (set in case of an intersection) of streets in which a certain violation occured
fun getStreetsFromViolation[v:Violation] : set Street{
    v.address.streets
}
--LSAs can schedule only violations that occur in their competence areas
fact LSACompetenceArea{
    all sv:ScheduledViolation | one s:getStreetsFromViolation[sv] | s in sv.scheduler.competenceArea
}

--Every location must be at least in one street and viceversa, every street must contain at least one location in order to be valid
fact LocationInStreet{
    all l:Location | some s:Street | s in l.streets and l in s.locations
}

--Every mining request must be associated to a response
fact OneResponsePerRequest{
    all re:MiningRequest | one rs:MiningResponse | rs.request=re
}

--A suggested intervention can be generated only if at least one violation occured in the same place
fact AtLeastOneViolationSuggestedIntervention{
    all si:SuggestedIntervention| some vi:Violation | si.location=vi.address
}

--Every id must be associated to the relative entity
fact NoDanglingIds{
    (all id:IdTechnician | some te:Technician | te.idNumber=id)
    and
    (all iv:IdViolation | some v:Violation | v.id=iv)
}

--Every password must be associated to the relative account
fact NoDanglingPassw{
    all p:Password | some a:Account | a.password=p
}

--Every InterventionCause must be associated to the relative SuggestedIntervention
fact NoDanglingIntCauses{
    all ic:InterventionCause | some si:SuggestedIntervention | si.reason=ic
}

--Every plate,model and brand of a vehicle must be associated to the relative vehicle
fact NoDanglingVehicleParams{
    all p:Plate | some v:Vehicle | v.plate=p
    and
    all m:Model | some v:Vehicle | v.model=m
    and
    all b:Brand | some v:Vehicle | v.brand=b
}

--Every parameter must be associated to the relative mining request
fact NoDanglingParams{
    all p:Parameter | some re:MiningRequest | p in re.parameters
}

--Every result must be associated to the relative mining response
fact NoDanglingResults{
    all r:Result | some mr:MiningResponse | mr.result=r
}

pred world1{
    #Street=2
    #Location=2
    #Coordinates=2
    #Violation=2
    #Vehicle=1
    #Date=2
    #User=1
    some disj s1,s2:Street | s1!=s2 and some l1:Location | l1 in s1.locations and not l1 in s2.locations
    and some disj v1,v2:Violation |  v1.address!=v2.address and v1.date!=v2.date
    and some disj c1,c2:Coordinates | c1.x!=c2.x and c1.y!=c2.y and c1.y!=c2.x and c2.x!=c1.y
}
run world1 for 2 but 0 LSA, 0 Technician

pred world2{
    #Technician=1
    #User=1
    #MiningRequest=2
    #MiningResponse=2
    #Result=2
    #Vehicle=0
    #Brand=0
    #Date=0
    #Model=0
    some disj m1,m2:MiningRequest | some disj mr1,mr2:MiningResponse| m1.topic=PlateTopic and m2.topic=MDSTopic and
     m1.miner!=m2.miner and #m1.parameters<3 and #m2.parameters<3 and mr1.request=m1 and mr2.request=m2
     and some u:User| m2.miner=u
    
}
run world2 

pred world3{
    #ScheduledViolation=1
    #Technician=1
    #Coordinates=1
    #SolvedViolation=0
    #PendingViolation=0
    #Parameter=0
    #Vehicle=1
    #SuggestedIntervention=0
    }

run world3

pred world4{
    #SuggestedIntervention=2
    #Violation=2
    some disj si1,si2:SuggestedIntervention | si1.location!=si2.location
}

run world4