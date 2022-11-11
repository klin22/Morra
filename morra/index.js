import React from 'react';
import AppViews from './views/AppViews';
import DeployerViews from './views/DeployerViews';
import AttacherViews from './views/AttacherViews';
import {renderDOM, renderView} from './views/render';
import './index.css';
import * as backend from './build/index.main.mjs';
import { loadStdlib } from '@reach-sh/stdlib';
import { ALGO_MyAlgoConnect as MyAlgoConnect } from '@reach-sh/stdlib'; 

const reach = loadStdlib(process.env)

reach.setWalletFallback(reach.walletFallback({
  providerEnv: 'TestNet', MyAlgoConnect }));

const intToOutcome = ['Deployer Wins!', 'Draw!', 'Attacher Wins!'];
const {standardUnit} = reach;
const defaults = {defaultFundAmt: '10', defaultWager: '3', standardUnit};

class App extends React.Component {
    constructor(props) {
      super(props);
      this.state = {view: 'ConnectAccount', ...defaults};
    }
    async componentDidMount() {
      const acc = await reach.getDefaultAccount();
      const balAtomic = await reach.balanceOf(acc);
      const bal = reach.formatCurrency(balAtomic, 4);
      this.setState({acc, bal});
      if (await reach.canFundFromFaucet()) {
        this.setState({view: 'FundAccount'});
      } else {
        console.log("set state to deployerorattacher");
        this.setState({view: 'DeployerOrAttacher'});
      }
    }
    async fundAccount(fundAmount) {
      await reach.fundFromFaucet(this.state.acc, reach.parseCurrency(fundAmount));
      this.setState({view: 'DeployerOrAttacher'});
    }
    async skipFundAccount() { this.setState({view: 'DeployerOrAttacher'}); }
    selectAttacher() { this.setState({view: 'Wrapper', ContentView: Attacher}); }
    selectDeployer() { this.setState({view: 'Wrapper', ContentView: Deployer}); }
    render() { return renderView(this, AppViews); }
  }

class Player extends React.Component{
    random() { return reach.hasRandom.random();}
    async getHand() {
        const hand = await new Promise(resolveHandP =>{
            this.setState({view: 'GetHand', playable: true, resolveHandP});
        });        
        this.setState({view: 'WaitingForResults', hand});
        return hand;
    }
    async getPrediction() {
        const prediction = await new Promise(resolvePredictionP =>{
            this.setState({view: 'GetPrediction', playable: true, resolvePredictionP});
        });
        this.setState({view: 'WaitingForResults', prediction})
        return prediction;
    }
    seeOutcome(i) { this.setState({view: 'Done', outcome: intToOutcome[i]});}
    informTimeout() {this.setState({view: 'Done', outcome: intToOutcome[i]});}
    playHand(hand) {this.state.resolveHandP(hand);} 
    makePrediction(prediction) {this.state.resolvePredictionP(prediction);}
    
}

class Deployer extends Player
{
    constructor(props)
    {
        super(props);
        this.state = {view: 'SetWager'}
    }
    setWager(wager) { 
      console.log("set wager"); 
      this.setState({view: 'Deploy', wager}); 
    }
    async deploy() {
      console.log("Deploying");
        const ctc = this.props.acc.contract(backend);
        this.setState({view: 'Deploying', ctc});

        this.wager = reach.parseCurrency(this.state.wager); 
        this.deadline = {ETH: 10, ALGO: 100, CFX: 1000}[reach.connector]; 
        backend.p1(ctc, this);
        const ctcInfoStr = JSON.stringify(await ctc.getInfo(), null, 2);        
        this.setState({view: 'WaitingForAttacher', ctcInfoStr});
    }
    
    render() { return renderView(this, DeployerViews); }
}
class Attacher extends Player {
    constructor(props) {
      super(props);
      this.state = {view: 'Attach'};
    }
    attach(ctcInfoStr) {
      const ctc = this.props.acc.contract(backend, JSON.parse(ctcInfoStr));
      this.setState({view: 'Attaching'});
      backend.p2(ctc, this);
    }
    async acceptWager(wagerAtomic) { 
      const wager = reach.formatCurrency(wagerAtomic, 4);
      return await new Promise(resolveAcceptedP => {
        this.setState({view: 'AcceptTerms', wager, resolveAcceptedP});
      });
    }
    termsAccepted() {
      this.state.resolveAcceptedP();
      this.setState({view: 'WaitingForTurn'});
    }
   
    render() { return renderView(this, AttacherViews); }
  }
  
  renderDOM(<App />);
