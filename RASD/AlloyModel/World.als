//SIGNATURES
abstract sig ReservationType{}
one sig Booked extends ReservationType{}
one sig ASAP extends ReservationType{}

abstract sig ReservationStatus{}
one sig Pending extends ReservationStatus{}
one sig Called extends ReservationStatus{}
one sig Discarded extends ReservationStatus{}
one sig Validated extends ReservationStatus{}

sig Date{}

sig Notification {
	timestamp: one Int,
	reservation: one Reservation
}

sig VisitStatistic {
	visitedDepartments: set Department, 
	timeInside: Int
}

sig UID{}
sig password{}

abstract sig Registration{
	uid: one UID,
	pwd: one password
}

sig Customer extends Registration {
	customerRes: set Reservation,
	notifications: set Notification
}

sig StoreManager extends Registration {
	store: one Store
}

sig Store {
	storeDeps: some Department,
	reservations: set Reservation,
	calledReservations: set Reservation,
	enteredReservations: set Reservation,
	maximumBookingsPerClient: Int,
	closedDates: set Date,
	currentDate : Date
} {
	reservations & calledReservations & enteredReservations = none
	currentDate not in closedDates
	all r: enteredReservations | r.status = Validated
	all r: storeDeps.inside | r in enteredReservations
	all r: storeDeps.inside | r.date = currentDate
}

sig Reservation {
	status: one ReservationStatus,
	date: one Date,
	type: one ReservationType,
	departments: some Department,
	store: one Store,
	callTimestamp: lone Int,
	enterTimestamp: lone Int,
	exitTimestamp: lone Int,
} {
	all disj d1, d2: departments | d1 != d2
	all d: departments | d in store.storeDeps
	all s: Store | s != store implies no d: s.storeDeps | d in departments

	status = Validated iff callTimestamp != none and enterTimestamp != none and exitTimestamp != none and 
	callTimestamp < enterTimestamp and enterTimestamp < exitTimestamp

	status in (Discarded + Called) iff callTimestamp != none and enterTimestamp = none and exitTimestamp = none

	status = Pending iff callTimestamp = none and enterTimestamp = none and exitTimestamp = none

	date & store.closedDates = none
	status = Validated implies this in store.enteredReservations
}

sig Department{
	maxBook: one Int,
	capacity: one Int,
	inside: some Reservation
} {
	#inside <= capacity
	#inside.type -> Booked <= maxBook
	maxBook <= capacity
	all disj r1, r2: inside | r1 != r2
	all r: inside | r.status = Validated
}

//FACTS
fact noRegistrationWithSameUID {
	all disj r1, r2: Registration | r1.uid != r2.uid
}


fact noASAPOtherTheDay {
	all s: Store | no r: s.reservations | r.type = ASAP and r.date != s.currentDate
}

fact OneToOneCustomerReservationsAndNotifications {
	(all disj c1, c2: Customer | 
		c1.customerRes & c2.customerRes = none and
		c1.notifications & c2.notifications = none)
	and (all r: Reservation | one c: Customer | r in c.customerRes)
}

fact calledReservationNotInStore {
	all s: Store |
		all r: s.calledReservations |
			no d: s.storeDeps | r in d.inside
}

fact oneASAPPerCustomer {
	all s: Store | no disj r, r': s.reservations | one c:Customer | r in c.customerRes and r' in c.customerRes and r.date = r'.date and r.type = ASAP and r'.type = ASAP
}

fact noSameDepartmentAcrossDifferentStores {
	all disj s, s' : Store | s.storeDeps & s'.storeDeps = none
}

fact onlyValidatedInsideTheStore {
	all d: Department | all r: d.inside | r.status = Validated
}

fact noStoreWithoutManager {
	all s: Store | one m: StoreManager | m.store = s
}

fact noCustomerWithMoreThanAllowedBookings {
	all c: Customer |
		all r: c.customerRes |
			all s: Store |
				#(r.store -> s) < s.maximumBookingsPerClient and r.type = Booked
}

fact allNotificationSentBeforeCallTime {
	all n: Notification | one r: Reservation | n.timestamp < r.callTimestamp and
	all r: Reservation | one n: Notification | n.reservation = r
}

fact noStoresWithSameReservation {
	all disj s1, s2: Store |
		(s1.reservations + s1.calledReservations + s1.enteredReservations) &
		(s2.reservations + s2.calledReservations + s2.enteredReservations) = none
}


fact noStoreWithSomeOtherStoreReservation {
	no s: Store |
		all r: Reservation |
			r.store != s and r in (s.reservations + s.calledReservations + s.enteredReservations)
}

fact noDepartmentWithoutStore {
	all d: Department | one s: Store | d in s.storeDeps
}

fact reservationStatus {
	all r: Reservation |
		(r.status = Pending implies
			r in r.store.reservations and
			not r in r.store.calledReservations and
			not r in r.store.enteredReservations) and
		(r.status = Called implies
			not r in r.store.reservations and
			r in r.store.calledReservations and 
			not r in r.store.enteredReservations) and
		(r.status = Validated implies
			one v: VisitStatistic | v.timeInside = r.enterTimestamp - r.exitTimestamp and 
			v.visitedDepartments = r.departments and
			not r in r.store.reservations and
			not r in r.store.calledReservations and
			r in r.store.enteredReservations 
			) and
		(
			r.status = Discarded implies
			not r in r.store.reservations and
			not r in r.store.calledReservations and
			not r in r.store.enteredReservations
		)
}


fact onlyReservationsOfTheDay {
	all s: Store | all r: s.calledReservations | r.date = s.currentDate
}

fact noCustomerOverlappingReservations {
	all c: Customer | no disj r1, r2: c.customerRes |
		r1.date = r2.date and (r1.enterTimestamp > r2.enterTimestamp and r1.exitTimestamp < r2.exitTimestamp)
}

//FUNCTIONS
fun getCustomerStatistics[s: Store, c: Customer]: set VisitStatistic {
	{stat : VisitStatistic |
		all r: s.enteredReservations |
			r in c.customerRes and stat.visitedDepartments = r.departments and
			stat.timeInside = r.exitTimestamp - r.enterTimestamp
	}	
}

//at this point of the specification document, no algorithm to intepretate departments'
//statistics has been described or implemented, so that here the function will return 
//only the client visit time in a visit including the department, 
//just to model the functionality of getting departments statistics

fun getDepartmentStatistic[d: Department, s: Store]: set Int {
	{
		i: Int |
			all r: s.enteredReservations |
				d in r.departments and i = r.exitTimestamp - r.enterTimestamp
	}
}

pred checkModel() {
#Customer >= 3
#StoreManager >= 3
#Store >= 3
#Store.storeDeps >= 2
#Reservation >= 6
#Department >= 2
#Reservation.departments >= 2
#Store.closedDates >= 1
#Date >= 3
}

run checkModel for 12

