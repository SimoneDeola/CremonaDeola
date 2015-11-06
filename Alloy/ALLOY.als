module myTaxiService


/* +++Class+++ */

/* "utility" classes*/

abstract sig boolean{}

one sig True extends boolean {}

one sig False extends boolean {}

abstract sig Time{
year: Int,
day: Int,
month: Int,
hour: Int,
minute : Int
}

abstract sig State{}

one sig NOT_HANDLED extends State{}

one sig HANDLED extends State{}

one sig ENDED extends State{}

/*"real" classes*/

sig Position{
long : one Int ,
lat : one Int
}

sig Zone{
range : one Int,
center : one Position
}

sig RegisteredUser{
userName : one String,
email : one String,
psw : one String,
badEvaluCount : one Int
}

sig Customer extends RegisteredUser{

}

sig TaxiDriver extends RegisteredUser{
licenseNumber : one Int,
availability : one boolean,
taxiId : one Int
}

sig Ride{
from : one Position,
state : one State,
requetingUser : one Customer,
taxiDriver: one TaxiDriver,

}

sig Reservation extends Ride{
to : one Position,
when : one Time
}

sig HandlingNotification{
customer : one Customer,
taxiDriver : one TaxiDriver,
waitingTime : one Int
}

sig Queue{
taxiDrivers : set TaxiDriver,
zone : one Zone,
rideOnThisQueue : set Ride
}


/* +++ Constrains +++ */
fact userNameUnicity{
no disj user1, user2 : RegisteredUser | user1.userName = user2.userName
}

fact eMailUnicity{
no disj user1, user2 : RegisteredUser | user1.email = user2.email
}

fact licenseNumberUnicity{
no disj user1, user2 : TaxiDriver | user1.licenseNumber = user2.licenseNumber
}


fact taxiIDUnicity{
no disj user1, user2 : TaxiDriver | user1.taxiID = user2.taxiID
}

fact differentCenterZone{
no disj zone1, zone2 : Zone | zone1.center = zone2.center
}

fact onlyAQueueForZone{
no disj queue1, queue2 : Queue | queue1.zone = queue2.zone
}


