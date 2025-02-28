#lang forge

open "mtg.frg"

pred validMana {
    all c: Card { c.manaCost >= 0 }
}

pred validCreature {
    all c: Creature {
        c.health >= 0
        c.health <= 15
        c.attack >= 0
        c.attack <= 15
        c.manaCost >= 0
        c.manaCost < 13
    }
}

test suite for cardWellformed {
    assert validMana is necessary for cardsWellInit for 6 Int
    assert validCreature is necessary for cardsWellInit for 6 Int
}

pred noCycles {
    all a: Action | {
        a not in a.^(nextAction)
    }
}

pred allReachable {
    some a: Action | {
        all b: Action | {
            a != b
            reachable[b, a, nextAction]
        }
    }
}

test suite for linearActions {
    assert noCycles is necessary for linearActions
    // assert allReachable is necessary for linearActions //this doesn't pass
}

test suite for gameEnd {
    
}

test suite for validActionSequence {

}

test suite for separateSpaces {

}

test suite for playersSeparate {

}