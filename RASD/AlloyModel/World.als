//SIGNATURES
abstract sig ReservationType{}
one sig Booked extends ReservationType{}
one sig ASAP extends ReservationType{}

abstract sig ReservationStatus{}
one sig Pending extends ReservationStatus{}
one sig Called extends ReservationStatus{}
one sig Discarded extends ReservationStatus{}
one sig Validated extends ReservationStatus{}

abstract sig MerchType{}

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
	maximumBookingsPerClient: Int
} {
	reservations & calledReservations & enteredReservations = none
}

sig Reservation {
	status: one ReservationStatus,
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
	callTimestamp != none and enterTimestamp != none implies callTimestamp < enterTimestamp
	enterTimestamp != none and exitTimestamp != none implies enterTimestamp < exitTimestamp
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
}

//FACTS
fact noRegistrationWithSameUID {
	all disj r1, r2: Registration | r1.uid != r2.uid
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

fact noTbcReservationsInStore {
	all s: Store |
		all r: s.reservations |
			no d: s.storeDeps | r in d.inside
}

fact noStoreWithoutManager {
	all s: Store | one m: StoreManager | m.store = s
}

fact noCustomerWithMoreThanAllowedBookings {
	all c: Customer |
		all r: c.customerRes |
			all s: Store |
				#(r.store -> s) < s.maximumBookingsPerClient
}


fact allNotificationSentBeforeCallTime {
	all n: Notification | one r: Reservation | n.timestamp < r.callTimestamp
}

fact noStoresWithSameReservation {
	all disj s1, s2: Store |
		(s1.reservations + s1.calledReservations + s1.enteredReservations) &
		(s2.reservations + s2.calledReservations + s2.enteredReservations) = none
}

fact noStoreWithSomeOtherStore {
	no s: Store |
		all r: Reservation |
			r.store != s and r in (s.reservations + s.calledReservations + s.enteredReservations)
}

fact reservationStatus {
	all r: Reservation |
		(r.status = Pending iff
			r.callTimestamp = none and 
			r.enterTimestamp = none and 
			r.exitTimestamp = none and
			r in r.store.reservations and
			not r in r.store.calledReservations and
			not r in r.store.enteredReservations) or
		(r.status = Called iff
			r.callTimestamp != none and
			r.enterTimestamp = none and 
			r.exitTimestamp = none and
			not r in r.store.reservations and
			r in r.store.calledReservations and 
			not r in r.store.enteredReservations) or 
		(r.status = Validated iff
			one v: VisitStatistic | v.timeInside = r.enterTimestamp - r.exitTimestamp and 
			v.visitedDepartments = r.departments and
			r.callTimestamp != none and
			r.enterTimestamp != none and
			r.exitTimestamp != none and
			not r in r.store.reservations and
			not r in r.store.calledReservations and
			r in r.store.enteredReservations 
			) or 
		(
			r.status = Discarded iff
			r.callTimestamp != none and
			r.enterTimestamp = none and
			r.exitTimestamp = none and
			not r in (r.store.reservations + r.store.calledReservations + r.store.enteredReservations)
		)
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
//statisticks has been described or implemented, so that here the function will return 
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
#Reservation >= 7
#Department >= 2
}

run checkModel for 10
