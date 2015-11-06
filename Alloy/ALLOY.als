module myTaxiService

/*************************************************/
/*              SETS (ENUMERATIONS)              */
/*************************************************/
enum RideState { NOT_HANDLED, HANDLED, ENDED }

/*************************************************/
/*                UTILITY SIGNATURES             */
/*************************************************/

abstract sig boolean{}
one sig True extends boolean {}
one sig False extends boolean {}

abstract sig Time{}

sig Integer{}
sig Strings{}

/*************************************************/
/*                MODEL CLASSES                  */
/*************************************************/

/* Position has   */
/* No constraints */
sig Position{
	long : one Integer,
	lat  : one Integer,
	isIn : one Zone
}

/* Zone is a piece of the city                                     */
/* it is a quadrilateral shape, so it's characterized by 4 corners */
sig Zone{
	upperLeftCorners  : one Position,
	upperRightCorners : one Position,
	lowerLeftCorners  : one Position,
 	lowerRightCorners : one Position
}


/* RegisteredUser is the basic user class in the model. */
/* it has an username                                   */
/* it has a password                                    */
/* it has an email                                      */
/* it has a position */
/* it has a zone     */
/*  FACTS:                   */
/* - email must be unique    */
/* - username must be unique */
/* - currentPosition of the user is in a certain zone if the user is in that zone. */
sig RegisteredUser{
	userName      : one Strings,
	email         : one Strings,
	psw           : one Strings,
	badEvaluCount : one Integer,
	currentPosition : one Position,
	currentZone     : one Zone
}

/* customer is the specialization of registered user. 
	it has a customerId

	FACTS
	customerId must be unique
*/
sig Customer extends RegisteredUser{
	customerId : one Integer
}

/* taxi driver is the specialization of registered user.
	it has licenseNumber
	it has availability
	it has taxiId
	it has a priority

	FACTS
	- license number must be unique
	- taxiId must be unique
*/
sig TaxiDriver extends RegisteredUser{
	licenseNumber : one Integer,
	availability  : one boolean,
	taxiId        : one Integer,
	priority      : one Integer
}

/* ride is a taxi request made by a customer
	it has a "from" position
	
	FACTS
	- if state is NOT_HANDLED taxiDriver is empty
	- if state is HANDLED or ENDED taxiDriver is not empty
*/
sig Ride{
	from : one Position,
	state : one RideState,
	requestingUser : one Customer,
	taxiDriver: lone TaxiDriver,
}

/*
	FACTS
	- from position must be the requestingUser current position.
*/
sig NormalRide extends Ride{
}

sig Reservation extends Ride{
	to : one Position,
	when : one Time
}

/***********/
/*  FACTS  */
/***********/
// "UNIQUE" - FACTS

/* +++ Constrains +++ */

//_____________________________________________________________________________
//REGISTERED USER FACTS
// - username must be unique
fact userNameUnicity{
	no disj user1, user2 : RegisteredUser | user1.userName = user2.userName
}

// - email must be unique
fact eMailUnicity{
	no disj user1, user2 : RegisteredUser | user1.email = user2.email
}

//* - currentPosition of the user is in a certain zone if the user is in that zone. */
fact positionInZone{
	all r : RegisteredUser | some p : Position |
		 p = r.currentPosition  implies p.isIn = r.currentZone
}

//_____________________________________________________________________________
// CUSTOMER FACTS
// - customerID must be unique
fact customerIDUnique{
	no disj c1, c2 : Customer | c1.customerId = c2.customerId
}

//_____________________________________________________________________________
// RIDES FACTS
//	- if state is NOT_HANDLED taxiDriver is empty
fact RideStateNotHandled{
	all r : Ride | r.state = NOT_HANDLED implies no r.taxiDriver 
}
//	- if state is HANDLED or ENDED taxiDriver is only one
fact RideStatHandledEnded{
	all r : Ride | r.state = HANDLED or r.state = ENDED implies #r.taxiDriver = 1
}

//_____________________________________________________________________________
// NORMAL RIDES FACTS
// - from position must be the requestingUser current position.
fact rideStartIsCustomerCurrentPosition{
	all r : NormalRide | r.from  = r.requestingUser.currentPosition
}

//_____________________________________________________________________________
// TAXI RELATED FACTS
// - Taxi license must be unique
fact licenseNumberUnicity{
no disj user1, user2 : TaxiDriver | user1.licenseNumber = user2.licenseNumber
}

// - Taxi number must be unique
fact taxiIDUnicity{
no disj user1, user2 : TaxiDriver | user1.taxiId = user2.taxiId
}

pred show {}

run show for 5
