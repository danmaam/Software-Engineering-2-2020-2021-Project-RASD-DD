//SIGNATURES
abstract sig ReservationType{}
one sig Booked extends ReservationType{}
one sig ASAP extends ReservationType{}

sig UID{}
sig password{}

abstract sig Registration{
	uid: one UID,
	pwd: one password
}

sig Customer extends Registration {
	reservations: set Reservation
} 

sig StoreManager extends Registration {
	store: one Store
}


sig Store {
	storeDeps: some Department,
	tbcReservations: set Reservation,
	calledReservations: set Reservation,
	
} {
	tbcReservations & calledReservations = none
}

sig Reservation {
	type: one ReservationType,
	departments: some Department,
	store: one Store
} {
	all disj d1, d2: departments | d1 != d2
	all d: departments | d in store.storeDeps
	all s: Store | s != store implies no d: s.storeDeps | d in departments
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
fact noCustomersWithSameUID {
	all disj c1, c2: Customer | c1.uid != c2.uid
}

fact noManagersWithSameUID {
	all disj m1, m2: StoreManager | m1.uid != m2.uid and m1.store != m2.store
}

fact OneToOneCustomerReservations {
	(all disj c1, c2: Customer | c1.reservations & c2.reservations = none)
	and (all r: Reservation | one c: Customer | r in c.reservations)
}

fact OneToOneStoreReservations {
	
}

fact calledReservationNotInStore {
	all s: Store |
		all r: s.calledReservations |
			no d: s.storeDeps | r in d.inside
}

fact noTbcReservationsInStore {
	all s: Store |
		all r: s.tbcReservations |
			no d: s.storeDeps | r in d.inside
}

fact noStoreWithoutManager {
	all s: Store | one m: StoreManager | m.store = s
}


pred checkModel() {
#Customer = 2
#StoreManager = 3
#Store = 3
#Reservation = 6
#Department >= 2
}

run checkModel for 6
