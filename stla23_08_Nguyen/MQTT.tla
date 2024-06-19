--------- MODULE MQTT -------
EXTENDS Integers, Sequences

CONSTANT MaxPacketId

VARIABLES producer, broker, consumer, packetIds

Init ==
    /\ producer = <<>>
    /\ broker = <<>>
    /\ consumer = <<>>
    /\ packetIds = <<>>

TypeInvariant ==
    /\ producer \in Seq(Seq(Int))
    /\ broker \in Seq(Seq(Int))
    /\ consumer \in Seq(Seq(Int))
    /\ packetIds \in Seq(Int)
    /\ \A i, j \in DOMAIN packetIds : i # j => packetIds[i] # packetIds[j]
    /\ \A i \in DOMAIN producer : Len(producer[i]) = 1

ProduceMessage == 
    /\ producer' = Append(producer, <<Len(packetIds) + 1>>)
    /\ packetIds' = Append(packetIds, Len(packetIds) + 1)

BrokerReceiveMessage ==
    /\ IF Len(producer) > 0 
       THEN /\ broker' = Append(broker, <<Head(producer)[1]>>)
            /\ producer' = Tail(producer)
       ELSE /\ broker' = broker
    /\ packetIds' = packetIds

ConsumerReceiveMessage ==
    /\ IF Len(broker) > 0 
       THEN /\ consumer' = Append(consumer, <<Head(broker)[1]>>)
            /\ broker' = Tail(broker)
       ELSE /\ consumer' = consumer
    /\ packetIds' = packetIds

Next ==
    \/ ProduceMessage
    \/ BrokerReceiveMessage
    \/ ConsumerReceiveMessage

Property ==
    \A i \in DOMAIN producer : \E j \in DOMAIN consumer : consumer[j] = producer[i]


=================