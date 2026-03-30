package org.verifx.practical

import org.verifx.practical.Prover
import org.scalatest.FlatSpec

class ProofTests extends FlatSpec with Prover {
  "GCounter" should "be a CRDT" in {
    val proof = ("GCounter", "is_a_CvRDT")
    prove(proof)
  }

  "PNCounter" should "be a CRDT" in {
    val proof = ("PNCounter", "is_a_CvRDT")
    prove(proof)
  }

  "GSet" should "be a CRDT" in {
    val proof = ("GSet", "is_a_CvRDT")
    prove(proof)
  }

  "TwoPSet" should "be a CRDT" in {
    val proof = ("TwoPSet", "is_a_CvRDT")
    prove(proof)
  }

  "ORSet" should "be a CRDT" in {
    val proof = ("ORSet", "is_a_CmRDT")
    prove(proof)
  }

  "UWMap" should "be a CRDT" in {
    val proof = ("UWMap", "is_a_CvRDT")
    prove(proof)
  }

  "UWGCMap" should "be a CRDT" in {
    val proof = ("UWGCMap", "is_a_CvRDT")
    prove(proof)
  }
}
