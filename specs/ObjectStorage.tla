---- MODULE ObjectStorage ----
EXTENDS Network, TLC

CONSTANTS
    CREATED,
    COMPLETED,
    CANCELED

CONSTANTS
    CreateObjectRequest,
    CreateObjectResponse,
    ReadObjectRequest,
    ReadObjectResponse,
    WriteObjectRequest,
    WriteObjectResponse

VARIABLE
    objects

CreateObject(m) ==
    LET objectId == m.data.objectId IN
        /\ Assert(id \notin DOMAIN objects,
            "Attempting to create an existing object.")
        /\ m.type = CreateObjectRequest
        /\ \/ /\ objects' = objects (+) [objectId |-> CREATED]
              /\ ReplyOrTimeout(m, [
                     src |-> ObjectStorage,
                     dst |-> m.src,
                     type |-> CreateObjectResponse,
                     data |-> [status |-> SUCCESS]
                 ])
           \/ ReplyOrTimeout(m, [
                  src |-> ObjectStorage,
                  dst |-> m.src,
                  type |-> CreateObjectResponse,
                  data |-> [status |-> FAILED]
              ])

ReadObject(m) ==
    LET objectId == m.data.objectId IN
        /\ Assert(id \in DOMAIN objects,
            "Attempting to read a non-existent object.")
        /\ m.type = ReadObjectRequest
        /\ UNCHANGED objects
        /\ ReplyOrTimeout(m, [
                src |-> ObjectStorage,
                dst |-> m.src,
                type |-> ReadObjectResponse,
                data |-> [id |-> objectId, status |-> objects[objectId]]
            ])

WriteObject(m) ==
    LET objectId == m.data.objectId IN
        /\ Assert(objectId \in DOMAIN objects,
            "Attempting to write a non-existent object.")
        /\ Assert(objects[objectId] = CREATED,
            "Attempting to write an " \o ToString(objects[objectId]) \o" object.")
        /\ m.type = WriteObjectRequest
        /\ \/ /\ objects' = [objets EXCEPT ![objectId] = COMPLETED]
              /\ ReplyOrTimeout(m, [
                     src |-> ObjectStorage,
                     dst |-> m.src,
                     type |-> WriteObjectResponse,
                     data |-> [status |-> SUCCESS]
                 ])
           \/ ReplyOrTimeout(m, [
                  src |-> ObjectStorage,
                  dst |-> m.src,
                  type |-> WriteObjectResponse,
                  data |-> [status |-> SUCCESS]
              ])

ObjectStorageReceive(m) ==
    \/ CreateObject(m)
    \/ ReadObject(m)
    \/ WriteObject(m)

====