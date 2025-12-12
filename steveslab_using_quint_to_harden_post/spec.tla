---- MODULE spec ----
EXTENDS TLC

\* https://steveslab.substack.com/p/using-quint-to-harden-your-specifications but in TLA+

CONSTANTS Admins, Users

VARIABLES 
    \* Registered users
    users,
    \* User roles (only defined for registered)
    role,
    \* Status of user in lifecycle
    status,
    \* Has the user set a password?
    has_password,
    \* Logged-in tokens
    tokens

vars == <<users, role, status, has_password, tokens>>

RoleAdmin == "admin"
RoleRegular == "regular"

StatusActive == "active"
StatusInactive == "inactive"
StatusWaitList == "wait_list"
StatusWaitingConfirmation == "waiting_confirmation"

EmptyRecord == [x \in {} |-> 0]

Init ==
    /\  users = {}
    /\  role = [x \in Admins |-> RoleAdmin]
    /\  status = [x \in Admins |-> StatusActive]
    /\  has_password = Admins
    /\  tokens = {}

\* 
\* Helpers
\* 

IsAdmin(user_id) == 
    /\  user_id \in DOMAIN role
    /\  role[user_id] = RoleAdmin

IsActive(user_id) ==
    /\  user_id \in DOMAIN status
    /\  status[user_id] = StatusActive

\* 
\* Actions
\* 

\* Register -> user enters wait list
Register(user_id) ==
    /\  user_id \notin users
    /\  users' = users \union {user_id}
    /\  role' = (user_id :> RoleRegular) @@ role
    /\  status' = (user_id :> StatusWaitList) @@ status
    /\  UNCHANGED <<has_password, tokens>>

\* Admin approves -> wait for user confirmation
Approve(admin_id, user_id) ==
    /\  IsAdmin(admin_id)
    /\  user_id \in users
    /\  status[user_id] = StatusWaitList
    /\  status' = [status EXCEPT ![user_id] = StatusWaitingConfirmation]
    /\  UNCHANGED  <<users, role, has_password, tokens>>

\* User clicks email -> status is set to active
ConfirmEmail(user_id) ==
    /\  user_id \in DOMAIN status
    /\  status[user_id] = StatusWaitingConfirmation
    /\  status' = [status EXCEPT ![user_id] = StatusActive]
    /\  UNCHANGED <<users, role, has_password, tokens>>

\* Firs login -> set password and create token
FirstLogin(user_id) ==
    /\  IsActive(user_id)
    /\  user_id \notin has_password
    /\  has_password' = has_password \union {user_id}
    /\  tokens' = tokens \union {user_id}
    /\  UNCHANGED <<users, role, status>>

\* Subsequente login -> token produced again
Login(user_id) ==
    /\  IsActive(user_id)
    /\  user_id \in has_password
    /\  tokens' = tokens \union {user_id}
    /\  UNCHANGED <<users, role, status, has_password>>

\* User gets promoted to admin
Promote(admin_id, user_id) ==
    /\  IsAdmin(admin_id)
    /\  user_id \in users
    /\  role' = [role EXCEPT ![user_id] = RoleAdmin]
    /\  UNCHANGED <<users, status, has_password, tokens>>

\* Users gets demoted to inactive
Demote(admin_id, user_id) ==
    /\  IsAdmin(admin_id)
    /\  user_id \in users
    /\  status' = [status EXCEPT ![user_id] = StatusInactive]
    /\  UNCHANGED <<users, role, has_password, tokens>>

\* 
\* Formulas and invariants
\* 

Next ==
    \/  \E admin_id \in Admins, user_id \in Users:
            \/  Approve(admin_id, user_id)
            \/  Promote(admin_id, user_id)
            \/  Demote(admin_id, user_id)
    \/  \E user_id \in Users:
            \/  Register(user_id)
            \/  ConfirmEmail(user_id)
            \/  FirstLogin(user_id)
            \/  Login(user_id)


Spec == Init /\ [][Next]_vars

NoToken == tokens = {}

TokenProduced == tokens /= {}
====