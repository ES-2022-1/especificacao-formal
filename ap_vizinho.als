module ApVizinho


//---------------SIGNATURES---------------

one sig ApVizinho {
	-- Conjunto dos usuários do sistema.
	users: set User
}

sig User {
	reviews: set Review,
	announcements: set Announcement
}

sig Review {}

sig Announcement {
	address: one Address,
	vacancies: set Vacancy
}

sig Address {}

sig Vacancy {}

---------------PRED---------------

-- O usuário esta dentro de uma entidade ApVizinho
pred userApVizinho[u: User, ap: ApVizinho] {
	u in ap.users
}

-- O review pertence a um usuário passado
pred reviewInUser[r: Review, u: User] {
	r in u.reviews
}

-- O announcement pertence a um usuário passado
pred AnnouncementInUser[an: Announcement, u: User] {
	an in u.announcements
}

--O address passado pertence a aquele announcement
pred adressAnnouncement[a: Address, an: Announcement] {
	a = getAdressAnnouncement[an]
}

-- A Vacancy pertence a um Announcement passado
pred VacancyInAnnouncement[v: Vacancy, an: Announcement] {
	v in an.vacancies
}

---------------FUNCTIONS---------------

fun getAdressAnnouncement[an: Announcement]: one Address {
	an.address
}

---------------FACTS---------------

-- all users in apvizinho
fact allUsersInApVizinho {
	all u: User| one ap: ApVizinho | u in ap.users
}

-- Todos os announcements possuem zero ou mais vagas
fact todosAnnouncementsPossuemVacancy{
	all an: Announcement| some v: Vacancy| VacancyInAnnouncement[v, an]
}

-- a vacancy is unique and can only be in one announcement
fact vacancyUnico{
	all v: Vacancy| one an: Announcement| VacancyInAnnouncement[v, an]
}

-- an announcement is unique to a user
fact announcementUnico{
	all an: Announcement| one u: User| AnnouncementInUser[an, u]
}

-- a review is unique to a user
fact reviewUnico{
	all r: Review| one u: User| reviewInUser[r, u]
}

-- all announcements as one unique adress
fact allAnnouncementsHaveUniqueAdress{
	all an: Announcement| one a: Address| an.address = a
}

-- one user as zero or more announcements
fact oneUserHasZeroOrMoreAnnouncements{
	all u: User| some an: Announcement| AnnouncementInUser[an, u]
}

-- an address can only belong to one announcement
fact addressUnico{
	all a: Address| one an: Announcement| an.address = a
}

---------------ASSERTS---------------

assert todosUsersNoApVizinho {
	all u: User| one ap: ApVizinho | userApVizinho[u, ap]
}

assert announcementIsUniqueForUser {
	all u: User| some an: Announcement| AnnouncementInUser[an, u]
}

--- Para todos os anúncios, considerando usuários distintos, se um anúncio foi criado por um usário (pertence a ele)
--  ele não pode ter sido criado por outro usuário.
assert announcementUnico {
	all an: Announcement | all disj user1, user2: User | (AnnouncementInUser[an, user1] => !AnnouncementInUser[an, user2])
}

--- Dois usuários distintos não possuem o mesmo review
assert reviewUnico {
	all r: Review | all disj user1, user2: User | (reviewInUser[r, user1] => !reviewInUser[r, user2])
}


pred show[] {}
run show for 5 Int

check todosUsersNoApVizinho for 10

check announcementUnico for 10

check announcementIsUniqueForUser for 10

check reviewUnico for 10

