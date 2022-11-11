'reach 0.1';

const[isOutcome, P1_WINS, DRAW, P2_WINS] = makeEnum(3);

const winner = function(hand1, hand2, prediction1, prediction2)
{
    
    const total = hand1 + hand2;

    const p1Correct = (prediction1 == total ? true : false);
    const p2Correct = (prediction2 == total ? true : false);

    if (!p1Correct && p2Correct)
    {
        return P2_WINS;
        
    }
    else if (p1Correct && !p2Correct)
    {
       return P1_WINS;
    }
    else 
    {
        return DRAW;
    }

}

assert(winner(0, 4, 0, 4) == P2_WINS);
assert(winner(4, 0, 4, 0) == P1_WINS);
assert(winner(0, 5, 0, 4) == DRAW);
assert(winner(1,2,1,2) == DRAW);

forall(UInt, playHandA =>
    forall(UInt, playHandB =>
      forall(UInt, gHandA =>
        forall(UInt, gHandB =>
          assert(isOutcome(winner(playHandA, playHandB, gHandA, gHandB)))))));
  
  forall(UInt, playHandA =>
    forall(UInt, playHandB =>
      forall(UInt, sameGuess =>
        assert(winner(playHandA, playHandB, sameGuess, sameGuess) == DRAW))));
  

const Player = {
    ...hasRandom,
    getHand: Fun([], UInt),
    getPrediction: Fun([], UInt),
    seeOutcome: Fun([UInt], Null),
    informTimeout: Fun([], Null),
    
};

export const main = Reach.App(() => {
    const Deployer = Participant('p1', {
        ...Player,
        wager:UInt,
        deadline: UInt,
        //getContinue: Fun([], Bool),

    });

    const Attacher = Participant('p2', {
        ...Player,
        acceptWager: Fun([UInt], Null),
        //acceptContinue: Fun([], Bool),
    });
    init();

    const informTimeout = () => {
        each([Deployer, Attacher], () => {
            interact.informTimeout();
        });
    }

    Deployer.only(() => {
        const wager = declassify(interact.wager);
        const deadline = declassify(interact.deadline);
    })

    Deployer.publish(wager, deadline)
        .pay(wager);
    commit();

    Attacher.only(() => {

        interact.acceptWager(wager);
    });

    Attacher.pay(wager)
        .timeout(relativeTime(deadline), () => closeTo(Deployer, informTimeout));

    var outcome = DRAW;

    invariant(balance() == 2 * wager && (outcome == DRAW || outcome == P1_WINS || outcome == P2_WINS));

    while ( outcome == DRAW )
    {
        commit();

        Deployer.only(() =>{
            const _handD = interact.getHand();
            const _predictionD = interact.getPrediction();
            const [_commitHandD, _saltHandD] = makeCommitment(interact, _handD);
            const [_commitPredictionD, _saltPredictionD] = makeCommitment(interact, _predictionD);

            const commitHandD = declassify(_commitHandD);
            const commitPredictionD = declassify(_commitPredictionD);
        });

        Deployer.publish(commitHandD, commitPredictionD)
            .timeout(relativeTime(deadline), () => closeTo(Attacher, informTimeout));

        commit();

        unknowable(Attacher, Deployer(_handD, _saltHandD));

        Attacher.only(()=> {
            const handA = declassify(interact.getHand());
            const predictionA = declassify(interact.getPrediction());
        });

        Attacher.publish(handA, predictionA)
            .timeout(relativeTime(deadline), () => closeTo(Deployer, informTimeout));
        commit();


        Deployer.only(() => {
            const [saltHandD, handD] = declassify([_saltHandD, _handD]);
            
            const [saltPredictionD, predictionD ] = declassify([_saltPredictionD, _predictionD ]);
            
        });

        Deployer.publish(saltHandD, handD, saltPredictionD, predictionD)
            .timeout(relativeTime(deadline), () => closeTo(Attacher, informTimeout));
        
        
        checkCommitment(commitHandD, saltHandD, handD);
        checkCommitment(commitPredictionD, saltPredictionD, predictionD)

        outcome = winner(handD, handA, predictionD, predictionA);
        continue;
    }

    assert(outcome == P1_WINS || outcome == P2_WINS);
    
    transfer(2*wager).to(outcome==P1_WINS ? Deployer : Attacher);
    
    commit();

    each([Attacher, Deployer], () => 
    {
        interact.seeOutcome(outcome);
    });

    exit();
});