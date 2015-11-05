module myTaxiService


/* +++Class+++ */

/* "utility" classes*/

abstract sig boolean{}

one sig True extends boolean {}

one sig False extends boolean {}

abstract sig Time{}

abstract sig State{}

/*"real" classes*/

sig Position{
long : one Int ,
lat : one Int
}

sig Zone{
range : one Int,
center : one Position
}

sig RegistredUser{
userName : one String,
email : one String,
psw : one String,
badEvaluCount : one Int
}

sig Customer extends RegistredUser{

}

sig TaxiDriver extends RegistredUser{
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

