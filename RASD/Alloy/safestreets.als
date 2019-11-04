abstract sig Account{
    userName: one String,
    password: one String
}{
    #password>8
}
sig User extends Account{}
sig LSA extends Account{
    availableTechnicians: set Technician,
    competenceArea: set Street
}
sig Technician extends Account{
    idNumber: one Int,
    agends:set Violation,
    boss: one LSA
}

sig MiningRequest{
    topic: one String,
    parameters: set String,
    miner: one Account
}
sig MiningResponse{
    violations:set Violation,
    request:MiningRequest

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
sig Street{
    location: set Location
}

sig Date{}

abstract sig ViolationStatus{}
one sig Pending extends ViolationStatus{}
one sig Scheduled extends ViolationStatus{}
one sig Solved extends ViolationStatus{}


sig Violation{
    id: Int,
    date: Date,
    address:Location,
    user: User,
    plate: String,
    status:ViolationStatus
}
sig ScheduledViolation{
    scheduler: one LSA,
    violation:one Violation,
    allocatedTechnicians: set Technician
}

sig Vehicle{
    plate:String,
    model:String,
    brand:String,
    violations: set Violation
}


fact differentUsernames{
    no disj a1,a2:Account | a1.userName=a2.userName
}

fact differentViolationIds{
    no disj v1,v2:Violation | v1.id=v2.id
} 

fact differentPlates{
    no disj v1,v2:Vehicle | v1.plate=v2.plate
}

fact differentTechnicianIds{
    no disj t1,t2 : Technician | t1.idNumber=t2.idNumber
}

--users can not make mining requests on car plates as only authorities are allowed to perform such queries
fact noUserPlateMining{
    all r:MiningRequest | r.topic="Plate" and 
    (no u:User | r.miner=u)
}

--users can not request other users violation in an explicit query
fact noOtherUsersViolation{
    all mr:MiningResponse | all m:mr.violations | mr.request.miner in User implies m.user=mr.request.miner
}

--All the available technician of a LSA must have as boss parameter the LSA himself
fact noDifferentBosses{
    all l:LSA | all t: Technician| t in l.availableTechnicians and t.boss=l
}

--Only the technicians' own boss can schedule them for a violation
fact ownBossScheduling{
    all sv:ScheduledViolation | all t:Technician | t in sv.allocatedTechnicians and t.boss=sv.scheduler
}

--Only pending violations can be scheduled: therefore, if a violation occurs on more than one street, only one among the LSAs which belongs to such competence areas can schedule his technicians.
fact pendingViolationScheduling{
    all sv:ScheduledViolation | sv.violation.status=Scheduled
}

fun getStreetsFromViolation[v:Violation] : set Street{
    v.address.streets
}
--LSAs can schedule only violations that occur in their competence areas
fact LSACompetenceArea{
    all sv:ScheduledViolation | one s:getStreetsFromViolation[sv.violation] | s in sv.scheduler.competenceArea
}

fact vehicleViolationAssociation{
    (all vi: Violation | one ve: Vehicle | vi.plate=ve.plate)
    and
    (all vi:Violation | some ve:Vehicle | vi in ve.violations)
}
pred show{

}
run show for 5