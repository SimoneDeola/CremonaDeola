module myTaxiService


/* +++Class+++ */

/* "utility" classes*/

abstract sig boolean{}
one sig True extends boolean {}
one sig False extends boolean {}

abstract sig Time{}
abstract sig State{}

sig Integer{}
sig Strings{}

/*"real" classes*/
/* */
sig Position{
	long : one Integer,
	lat : one Integer
}

sig Zone{
	edges : some Position,
	center : one Position
}{
	#edges = 4
}

sig RegisteredUser{
	userName : one String,
	email : one String,
	psw : one String,
	badEvaluCount : one Integer
}

sig Customer extends RegisteredUser{
	customerId : one Integer
}

sig TaxiDriver extends RegisteredUser{
	licenseNumber : one Integer,
	availability : one boolean,
	taxiId : one Integer
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
waitingTime : one Integer
}

sig Queue{
taxiDrivers : set TaxiDriver,
zone : one Zone,
rideOnThisQueue : set Ride
}

/***********/
/*  FACTS  */
/***********/
// "UNIQUE" - FACTS

/* +++ Constrains +++ */

// - username must be unique
fact userNameUnicity{
no disj user1, user2 : RegisteredUser | user1.userName = user2.userName
}

// - email must be unique
fact eMailUnicity{
no disj user1, user2 : RegisteredUser | user1.email = user2.email
}

// - Taxi license must be unique
fact licenseNumberUnicity{
no disj user1, user2 : TaxiDriver | user1.licenseNumber = user2.licenseNumber
}

// - Taxi number must be unique
fact taxiIDUnicity{
no disj user1, user2 : TaxiDriver | user1.taxiId = user2.taxiId
}


// TAXI RELATED FACTS


fact differentCenterZone{
no disj zone1, zone2 : Zone | zone1.center = zone2.center
}

fact onlyAQueueForZone{
no disj queue1, queue2 : Queue | queue1.zone = queue2.zone
}

pred show {}

run show for 5
