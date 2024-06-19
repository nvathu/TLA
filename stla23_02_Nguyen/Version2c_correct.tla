---- MODULE Version2c_correct ----
VARIABLE  chan

Inner(hr) == Version1 WITH hr <-hr
HiddenHrSpec == \EE hr: Spec
====