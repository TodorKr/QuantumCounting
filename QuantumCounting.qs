namespace QRL_App {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Convert;

    @EntryPoint()
    operation main() : Unit {
        let iterations = 100;
        let n = 4;
        let p = 7;
        mutable results = new Int[Round(PowD(2.0,IntAsDouble(n)))+2]; //theta results
        mutable m_results = new Int[Round(PowD(2.0,IntAsDouble(n)))+2]; // M results
        Message($"With precision p = {p} and state space n = {n}:");

        for (i in 1..iterations) {
            let (output_1, output_2)  = QuantumCounting(n,p);

            set results w/=(output_2) <- results[output_2] + 1;

            let m = PowD(2.0, IntAsDouble(n))*PowD(Cos(IntAsDouble(output_1)*PI()/PowD(2.0, IntAsDouble(p))), 2.0);
            set m_results w/=(Round(m)) <- m_results[Round(m)] + 1;
            //set m_results w/=(output_1) <- m_results[output_1] + 1;
        }

        for (i in 0..Length(m_results)-1) {
            if (m_results[i] > 0) {
                //Message($"M = {i}; Grover values: {results[i]}/{iterations}; Num of solutions: {m_results[i]}/{iterations}");
                Message($"Number of solutions M = {i}; Times obtained: {m_results[i]}/{iterations}");
            }
        }
    }

    operation Set (desired: Result, q1: Qubit) : Unit {
        if (desired != M(q1)) {
            X(q1);
        }
    }

    operation OR (q1: Qubit, q2: Qubit, output: Qubit) : Unit {
        using (aux = Qubit()) {
            Set(Zero, aux);

            CCNOT(q1,q2,aux);
            CNOT(q1,aux);
            CNOT(q2,aux);
            
        }
    }

    operation multiCNOT(ctrl: Qubit[], tgt: Qubit) : Unit {
        let qLength = Length(ctrl) - 1;

        //Use N-1 ancilla qubits (N = number of control qubits)
        using (anc = Qubit[qLength]) {

            //Initialize ancilla registers
            for (i in 0..qLength-1) {
                Set(Zero, anc[i]);
            }

            //Apply multiple controlled NOT
            CCNOT(ctrl[0], ctrl[1], anc[0]);
            if (qLength > 1) {
                for (i in 0..qLength-2) {
                    CCNOT(anc[i], ctrl[i+2], anc[i+1]);
                }
            }
            
            //Set the result of the multiple controlled not in target qubit
            CNOT(anc[qLength-1], tgt);

            //Apply the inverse operation to leave the control qubits in its original states
            if (qLength > 1) {
                for (i in 0..qLength-2) {
                    CCNOT(anc[qLength-2-i], ctrl[qLength-i], anc[qLength-i-1]);
                }
            }
            CCNOT(ctrl[0], ctrl[1], anc[0]);

            //Leave ancilla registers in state 0
            for (i in 0..qLength-1) {
                Set(Zero, anc[i]);
            }
        }
    }

    operation groverOperator (control: Qubit, target: Qubit[], flagQubit: Qubit) : Unit {
        
        //Uf: Amplifying target action probability
            //groverOracle(target, flagQubit, action);
        //Grover oracle:
        //CNOT(control, target[0]);
        //multiCNOT([control]+target[0..6], flagQubit); //Looking for 0111? => 2/32 solutions
        //CNOT(control, target[0]);

        //Grover oracle: x0x3 + (x1x2 # x0x1)
        using (aux = Qubit[2]) {
            //CCNOT(target[0], target[1], aux[0]); // x0 AND x1
            multiCNOT([control]+[target[0]]+[target[1]], aux[0]);
            //CCNOT(target[1], target[2], aux[0]); // x0x1 XOR x1x2
            multiCNOT([control]+[target[1]]+[target[2]], aux[0]);
            multiCNOT([control]+[target[0]]+[target[3]]+[aux[0]], aux[1]);
            //CCNOT(target[0], target[3], aux[0]);
            multiCNOT([control]+[target[0]]+[target[3]], aux[0]);

            CCNOT(control, aux[1], aux[0]);
            CCNOT(control, aux[0], flagQubit);
            CCNOT(control, aux[1], aux[0]);

            multiCNOT([control]+[target[0]]+[target[3]], aux[0]);
            multiCNOT([control]+[target[0]]+[target[3]]+[aux[0]], aux[1]);
            multiCNOT([control]+[target[1]]+[target[2]], aux[0]);
            multiCNOT([control]+[target[0]]+[target[1]], aux[0]);
            Set(Zero, aux[0]);
            Set(Zero, aux[1]);
        }

        //Hadamards
        for (qubit in target) {
            Controlled H([control], qubit);
        }

        //U0 orthogonal
        //ApplyToEachCA(X, target);
        for (qubit in target) {
            Controlled X([control], qubit);
        }

        if (Length(target) > 1) {
            multiCNOT([control]+target,flagQubit);
        }
        else {
            CNOT(target[0],flagQubit);
        }

        //ApplyToEachCA(X, target);
        for (qubit in target) {
            Controlled X([control], qubit);
        }

        //Hadamards
        //ApplyToEachCA(H, target);
        for (qubit in target) {
            Controlled H([control], qubit);
        }


    }

    operation QuantumCounting(n: Int, p: Int) : (Int, Int) {
        //Estimation precision p which error < 2^-(p+1)
        //let p = 3;
        //State space n where 2^n equals the total number of potential solutions
        //let n = 5;
        mutable theta_est = 0;
        mutable res = 0;

        using ((theta, x) = (Qubit[p], Qubit[n+1])) {
            //Define flag qubit for Grover operator
            let flagQubit = x[Length(x)-1];

            //Apply an equally weighted superposition of all qubits
            ApplyToEachCA(H, theta);
            ApplyToEachCA(H, x);
            Z(flagQubit);

            //Apply all controlled Grover operators according to QPE
            mutable grover_iterations = 1;
            for (j in 0..p-1) {
                for (i in 1..grover_iterations) {
                    groverOperator(theta[j], x[0..Length(x)-2], flagQubit);
                }
                set grover_iterations = grover_iterations * 2;
            }

            //Apply QFT to obtain an estimation of theta, rotation angle corresponding to the number of solutions
            QFTLE(LittleEndian(theta));

            //Measure theta register to obtain the estimaton of theta
            //set theta_est = MeasureInteger(BigEndianAsLittleEndian(BigEndian(theta)));
            set theta_est = MeasureInteger(LittleEndian(theta));
            set res = MeasureInteger(BigEndianAsLittleEndian(BigEndian(x[0..Length(x)-2])));
            //set res = MeasureInteger(LittleEndian(x[0..Length(x)-2]));

            //Reset all used qubits
            ResetAll(theta);
            ResetAll(x);
        }

        //M = N * sin^2(theta*pi/2^p) = number of solutions of the given function
        //return PowD(2.0, IntAsDouble(n))*PowD(Sin(IntAsDouble(theta_est)*PI()/PowD(2.0, IntAsDouble(p))), 2.0);
        return (theta_est, res);
    }

    

}

