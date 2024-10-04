public class TarjansAlgorithmArrayRecursive {
    public int currentComp; // = 0
    public int stackPointer; // 0 indicates empty stack
    public int currentDFSNumber; // = 0

    public int[][] adjVertices; // adjVertices[i] has element j <=> edge from i to j
    public int[] dfsNumbers; // dfsNumbers[i] == -1 <=> no dfs number yet, not visited
    public int[] lowlinkNumbers; // lowlinkNumbers[i] == 1 <=> no dfs number yet, not visited

    public int[] stack;
    public int[] onStack; // onStack[i] == 1 <=> i is on the stack
    public int[] components; // components[i] == k <=> vertex i is in component k

    //@pure
    public int sumNeqVal(int[] arr, int val) {
        int sum = 0;
        for (int i : arr) {
            if (i != val) {
                sum++;
            }
        }
        return sum;
    }

    //@pure
    public int elementsOnStack(int[] arr) {
        int sum = 0;
        for (int i : arr) {
            if (i == 1) {
                sum++;
            }
        }
        return sum;
    }

    //@pure
    public int max(int[] arr) {
        int m = -1;
        for (int i : arr) {
            if (i > m) {
                m = i;
            }
        }
        return m;
    }

    //@pure
    public boolean reachable(int x,int y) {
        if (x == y) {
            return true;
        }
        if (adjVertices[x].length == 0) {
            return false;
        }
        boolean[] visited = new boolean[adjVertices.length];
        int[] queue = new int[adjVertices.length];
        int currentPointer = 0;
        int currentVertex;
        queue[currentPointer] = x;
        visited[x] = true;
        while (currentPointer != -1) {
            currentVertex = queue[currentPointer];
            currentPointer--;
            for (int neighbor : adjVertices[currentVertex]) {
                if (neighbor == y) {
                    return true;
                }
                if (!visited[neighbor]) {
                    currentPointer++;
                    queue[currentPointer] = neighbor;
                    visited[neighbor] = true;
                }

            }
        }
        return false;
    }
    //@pure
    public boolean inSameSCC(int x, int y) {
        return reachable(x,y) && reachable(y,x);
    }

    /*@ normal_behaviour
      @ // arrays are not null
      @ requires adjVertices != null;
      @ requires (\forall int i; 0 <= i < adjVertices.length; adjVertices[i] != null);
      @ requires dfsNumbers != null && lowlinkNumbers != null;
      @ requires stack != null && onStack != null;
      @ requires components != null;
      @ // length requirements
      @ requires adjVertices.length == dfsNumbers.length && adjVertices.length == lowlinkNumbers.length;
      @ requires adjVertices.length == stack.length && adjVertices.length == onStack.length;
      @ requires adjVertices.length == components.length;
      @ // adjVertices domain
      @ requires (\forall int i; 0 <= i < adjVertices.length;
      @                     (\forall int j; 0 <= j < adjVertices[i].length; 0 <= adjVertices[i][j] < adjVertices.length)
      @                  );
      @ // starting values of arrays
      @ requires (\forall int i; 0 <= i < dfsNumbers.length; dfsNumbers[i] == -1);
      @ requires (\forall int i; 0 <= i < lowlinkNumbers.length; lowlinkNumbers[i] == -1);
      @ requires (\forall int i; 0 <= i < onStack.length; onStack[i] == 0);
      @ requires (\forall int i; 0 <= i < components.length; components[i] == -1);
      @ // starting values of variables
      @ requires stackPointer == 0;
      @ requires currentDFSNumber == 0;
      @ requires currentComp == 0;
      @ // all vertices have assigned components
      @ ensures (\forall int i; 0 <= i < components.length; components[i] != -1);
      @ ensures (\forall int i; 0 <= i < components.length; (\forall int j; 0 <= j < components.length; (components[i] == components[j]) ==> inSameSCC(i,j)) &&
      @                                                     !(\exists int k; 0 <= k < components.length; components[i] != components[k] && inSameSCC(i,k)));
      @ assignable stackPointer, currentDFSNumber, currentComp;
      @ assignable dfsNumbers[*], lowlinkNumbers[*], stack[*], onStack[*];
      @*/
    public void startTarjans() {
        for (int i = 0; i < dfsNumbers.length; i++) {
            if (dfsNumbers[i] == -1) {
                this.dfs(i);
            }
        }
    }

    /*@ public normal_behaviour
      @ // arrays are not null
      @ requires adjVertices != null;
      @ requires  (\forall int i; 0 <= i < adjVertices.length; adjVertices[i] != null);
      @ requires dfsNumbers != null && lowlinkNumbers != null;
      @ requires stack != null && onStack != null;
      @ requires components != null;
      @ // length requirements
      @ requires adjVertices.length == dfsNumbers.length && adjVertices.length == lowlinkNumbers.length;
      @ requires adjVertices.length == stack.length && adjVertices.length == onStack.length;
      @ requires adjVertices.length == components.length;
      @ requires (\forall int i; 0 <= i < adjVertices.length;
      @                     (\forall int j; 0 <= j < adjVertices[i].length; 0 <= adjVertices[i][j] < adjVertices.length)
      @                  );
      @ requires (\forall int i; 0 <= i < components.length; -1 <= components[i] < currentComp);
      @ requires vertexLabel >= 0 && vertexLabel < adjVertices.length && onStack[vertexLabel] == 0 && dfsNumbers[vertexLabel] == -1 && components[vertexLabel] == -1;
      @ // on stack only 0 or 1
      @ requires (\forall int i; 0 <= i < onStack.length; onStack[i] == 0 || onStack[i] == 1);
      @ requires 0 <= currentComp < components.length;
      @ requires currentComp == max(components) + 1;
      @ requires currentDFSNumber == sumNeqVal(dfsNumbers, -1) && currentDFSNumber < dfsNumbers.length;
      @ requires stackPointer == elementsOnStack(onStack) && 0 <= stackPointer < stack.length;
      @ requires (\forall int i; 0 <= i < dfsNumbers.length; dfsNumbers[i] != -1 <==> lowlinkNumbers[i] != -1);
      @ requires (\forall int i; 0 <= i < dfsNumbers.length; -1 <= dfsNumbers[i] < adjVertices.length && -1 <= lowlinkNumbers[i] <= dfsNumbers[i]);
      @ // bounded dfsNumbers
      @ requires (\forall int i; 0 <= i < dfsNumbers.length; -1 <= dfsNumbers[i] < currentDFSNumber);
      @ // dfsNumber is -1 if not on stack and no component assigned yet
      @ requires (\forall int i; 0 <= i < dfsNumbers.length; !(onStack[i] == 1 || components[i] != -1) <==> dfsNumbers[i] == -1);
      @ //distinct elements in dfsNumbers except -1
      @ requires (\forall int i; 0 <= i < dfsNumbers.length; dfsNumbers[i] == -1 || (\forall int j; i < j < dfsNumbers.length; dfsNumbers[i] != dfsNumbers[j]));
      @ // bounded stack
      @ requires (\forall int i; 0 <= i < stackPointer; stack[i] < dfsNumbers.length);
      @ // distinct elements on stack till stackPointer
      @ requires (\forall int i; 0 <= i < stackPointer; (\forall int j; 0 <= j < stackPointer; (i != j) ==> (stack[i] != stack[j]) ));
      @ // stack sorted after dfsNumber
      @ requires (\forall int i; 0 <= i < stackPointer; (\forall int j; i < j < stackPointer; (i < j) <==> (dfsNumbers[stack[i]] < dfsNumbers[stack[j]])));
      @ // all vertices with assigned components have no reachable non-visited vertex
      @ requires (\forall int i; 0 <= i < components.length; (components[i] != -1) ==> (\forall int j; 0 <= j < adjVertices[i].length; (onStack[adjVertices[i][j]] == 1)|| components[adjVertices[i][j]] != -1));
      @
      @ // being on stack means no component yet
      @ requires (\forall int i; 0 <= i < onStack.length; onStack[i] == 1 ==> components[i] == -1);
      @ // assigned vertex is NOT on stack
      @ requires (\forall int i; 0 <= i < components.length; components[i] != -1 ==> onStack[i] == 0);
      @ // components assignment starting from 0
      @ requires (\forall int i; 0 <= i < currentComp; (\exists int k; 0 <= k < components.length; components[k] == i));
      @ // stack - onStack relation
      @ requires (\forall int i; 0 <= i < onStack.length; (onStack[i] == 1) <==> (\exists int k; 0 <= k < stackPointer; stack[k] == i));
      @ // vertexLabel is reachable from all stackElements
      @ requires (\forall int i; 0 <= i < stackPointer; reachable(stack[i], vertexLabel));
      @ // lowlinkVal becomes != -1 if dfsNumbersVal becomes != -1
      @ requires (\forall int i; 0 <= i < dfsNumbers.length; lowlinkNumbers[i] != -1 <==> dfsNumbers[i] != -1);
      @ // for every vertex on stack there is a reachable vertex with low == dfs
      @ requires (\forall int i; 0 <= i < stackPointer; (\exists int j; 0 <= j < stackPointer ;reachable(stack[i], stack[j]) && lowlinkNumbers[stack[j]] == dfsNumbers[stack[j]]));
      @ // is a scc\
      @ requires (\forall int i; 0 <= i < components.length; (\forall int j; 0 <= j < components.length; components[j] == -1 || components[i] == -1 || (components[i] == components[j] ==> inSameSCC(i,j))));
      @ requires (\forall int i; 0 <= i < components.length; !(\exists int j; 0 <= j < components.length; components[i] != -1 && components[i] != components[j] && inSameSCC(i, j)));
      @ ensures (\forall int i; 0 <= i < components.length; -1 <= components[i] < adjVertices.length);
      @ // dfsNumber is -1 if not on stack and no component assigned yet after execution
      @ ensures (\forall int i; 0 <= i < dfsNumbers.length; !(onStack[i] == 1 || components[i] != -1) <==> dfsNumbers[i] == -1);
      @ // stack still remains sorted after dfsNumber
      @ ensures (\forall int i; 0 <= i < stackPointer; (\forall int j; i < j < stackPointer; (i < j) <==> (dfsNumbers[stack[i]] < dfsNumbers[stack[j]])));
      @
      @ ensures (\forall int i; 0 <= i < components.length; (\forall int j; 0 <= j < components.length; components[i] == -1 || (components[i] == components[j] ==> inSameSCC(i,j))));
      @ ensures (\forall int i; 0 <= i < components.length; !(\exists int j; 0 <= j < components.length; components[i] != -1 && components[i] != components[j] && inSameSCC(i, j)));
      @ // more stack invariants
      @ ensures (\forall int i; 0 <= i < stackPointer; stack[i] < dfsNumbers.length);
      @ // distinct elements on stack till stackPointer
      @ ensures (\forall int i; 0 <= i < stackPointer; (\forall int j; 0 <= j < stackPointer; (i != j) ==> (stack[i] != stack[j]) ));
      @ // stack sorted after dfsNumber
      @ ensures (\forall int i; 0 <= i < stackPointer; (\forall int j; i < j < stackPointer; (i < j) <==> (dfsNumbers[stack[i]] < dfsNumbers[stack[j]])));
      @ // all vertices with assigned components have no reachable non-visited vertex
      @ ensures (\forall int i; 0 <= i < components.length; (components[i] != -1) ==> (\forall int j; 0 <= j < adjVertices[i].length; (onStack[adjVertices[i][j]] == 1)|| components[adjVertices[i][j]] != -1));
      @
      @ // lowlinkVal becomes != -1 if dfsNumbersVal becomes != -1
      @ ensures (\forall int i; 0 <= i < dfsNumbers.length; lowlinkNumbers[i] != -1 <==> dfsNumbers[i] != -1);
      @ // stack - onStack relation
      @ ensures (\forall int i; 0 <= i < onStack.length; (onStack[i] == 1) <==> (\exists int k; 0 <= k < stackPointer; stack[k] == i));
      @ // on stack only 0 or 1
      @ ensures (\forall int i; 0 <= i < onStack.length; onStack[i] == 0 || onStack[i] == 1);
      @ // vertexLabel is reachable from all stackElements
      @ ensures (\forall int i; 0 <= i < stackPointer; reachable(stack[i], vertexLabel));
      @ // for every vertex on stack there is a reachable vertex with low == dfs
      @ ensures (\forall int i; 0 <= i < stackPointer; (\exists int j; 0 <= j < stackPointer ;reachable(stack[i], stack[j]) && lowlinkNumbers[stack[j]] == dfsNumbers[stack[j]]));
      @ // dfs number still bounded
      @ ensures (\forall int i; 0 <= i < dfsNumbers.length; -1 <= dfsNumbers[i] < currentDFSNumber);
      @ assignable dfsNumbers[*], lowlinkNumbers[*], stack[*], onStack[*], components[*];
      @ assignable stackPointer, currentDFSNumber, currentComp;
      @*/
    public void dfs(int vertexLabel) {
        preDFS(vertexLabel);
        // visiting all neighbors
        for (int neighborVertexInd = 0; neighborVertexInd < adjVertices[vertexLabel].length; neighborVertexInd++) {
            int neighborVertex = adjVertices[vertexLabel][neighborVertexInd];

            if (dfsNumbers[neighborVertex] == -1) {
                dfs(neighborVertex);
                lowlinkNumbers[vertexLabel] = lowlinkNumbers[vertexLabel] <= lowlinkNumbers[neighborVertex] ? lowlinkNumbers[vertexLabel] : lowlinkNumbers[neighborVertex];
            } else if (dfsNumbers[neighborVertex] < dfsNumbers[vertexLabel] && onStack[neighborVertex] == 1) {
                lowlinkNumbers[vertexLabel] = lowlinkNumbers[vertexLabel] <= dfsNumbers[neighborVertex] ? lowlinkNumbers[vertexLabel] : dfsNumbers[neighborVertex];
            }
        }
        postDFS(vertexLabel);
    }


    /*@ public normal_behaviour
      @ // non-null and length requirements
      @ requires dfsNumbers != null && lowlinkNumbers != null && stack != null && onStack != null;
      @ requires dfsNumbers.length == lowlinkNumbers.length && dfsNumbers.length == stack.length && dfsNumbers.length == onStack.length;
      @ requires 0 <= vertexLabel < dfsNumbers.length;
      @ // enforcing current value of variables depending on array states
      @ requires currentDFSNumber == sumNeqVal(dfsNumbers, -1) && 0 <= currentDFSNumber < dfsNumbers.length;
      @ requires stackPointer == elementsOnStack(onStack) && 0 <= stackPointer < stack.length;
      @ ensures dfsNumbers[vertexLabel] == \old(currentDFSNumber);
      @ ensures lowlinkNumbers[vertexLabel] == \old(currentDFSNumber);
      @ ensures currentDFSNumber == \old(currentDFSNumber) + 1;
      @ ensures stackPointer == \old(stackPointer) + 1;
      @ ensures stack[\old(stackPointer)] == vertexLabel;
      @ ensures onStack[vertexLabel] == 1;
      @ assignable dfsNumbers[vertexLabel], lowlinkNumbers[vertexLabel], stack[stackPointer], onStack[vertexLabel];
      @ assignable stackPointer, currentDFSNumber;
      @*/
    public void preDFS(int vertexLabel) {
        dfsNumbers[vertexLabel] = currentDFSNumber;
        lowlinkNumbers[vertexLabel] = currentDFSNumber;
        currentDFSNumber++;

        stack[stackPointer] = vertexLabel;
        onStack[vertexLabel] = 1;
        stackPointer++;
    }


    /*@ public normal_behaviour
      @ // arrays are not null
      @ requires adjVertices != null;
      @ requires  (\forall int i; 0 <= i < adjVertices.length; adjVertices[i] != null);
      @ requires dfsNumbers != null && lowlinkNumbers != null && stack != null && onStack != null && components != null;
      @
      @ // length requirements
      @ requires adjVertices.length == dfsNumbers.length && adjVertices.length == lowlinkNumbers.length;
      @ requires adjVertices.length == stack.length && adjVertices.length == onStack.length;
      @ requires adjVertices.length == components.length;
      @ // enforcing current value of variables depending on array states
      @ requires currentComp == max(components) + 1 && 0 <= currentComp < components.length;
      @ requires stackPointer == elementsOnStack(onStack) && 0 <= stackPointer <= stack.length;
      @ // adjVertices domain
      @ requires (\forall int i; 0 <= i < adjVertices.length;
      @                     (\forall int j; 0 <= j < adjVertices[i].length; 0 <= adjVertices[i][j] < adjVertices.length)
      @                  );
      @ // components domain
      @ requires (\forall int i; 0 <= i < components.length; -1 <= components[i] < adjVertices.length);
      @ // stack domain
      @ requires (\forall int i; 0 <= i < stackPointer; 0 <= stack[i] < dfsNumbers.length);
      @ // array state starting conditions
      @ requires vertexLabel >= 0 && vertexLabel < adjVertices.length && onStack[vertexLabel] == 1 && dfsNumbers[vertexLabel] != -1 && components[vertexLabel] == -1;
      @ // dfsNumber is -1 if not on stack and no component assigned yet
      @ requires (\forall int i; 0 <= i < dfsNumbers.length; !(onStack[i] == 1 || components[i] != -1) <==> dfsNumbers[i] == -1);
      @ //distinct elements in dfsNumbers except -1
      @ requires (\forall int i; 0 <= i < dfsNumbers.length; dfsNumbers[i] == -1 || (\forall int j; i < j < dfsNumbers.length; dfsNumbers[i] != dfsNumbers[j]));
      @ // distinct elements on stack till stackPointer
      @ requires (\forall int i; 0 <= i < stackPointer; (\forall int j; i < j < stackPointer; (stack[i] != stack[j]) ));
      @ // stack sorted after dfsNumber
      @ requires (\forall int i; 0 <= i < stackPointer; (\forall int j; i < j < stackPointer; (i < j) <==> (dfsNumbers[stack[i]] < dfsNumbers[stack[j]])));
      @ // all vertices with assigned components have no reachable non-visited vertex
      @ requires (\forall int i; 0 <= i < components.length; (components[i] != -1) ==> (\forall int j; 0 <= j < adjVertices[i].length; (onStack[adjVertices[i][j]] == 1)|| components[adjVertices[i][j]] != -1));
      @
      @ // stack - onStack relation
      @ requires (\forall int i; 0 <= i < onStack.length; (onStack[i] == 1) <==> (\exists int k; 0 <= k < stackPointer; stack[k] == i));
      @ // on stack only 0 or 1
      @ requires (\forall int i; 0 <= i < onStack.length; onStack[i] == 0 || onStack[i] == 1);
      @ // vertexLabel is reachable from all stackElements
      @ requires (\forall int i; 0 <= i < stackPointer; reachable(stack[i], vertexLabel));
      @ // for every vertex on stack there is a reachable vertex with low == dfs
      @ requires (\forall int i; 0 <= i < stackPointer; (\exists int j; 0 <= j < stackPointer ;reachable(stack[i], stack[j]) && lowlinkNumbers[stack[j]] == dfsNumbers[stack[j]]));
      @ // is a scc\
      @ requires (\forall int i; 0 <= i < components.length; (\forall int j; 0 <= j < components.length; components[j] == -1 || components[i] == -1 || (components[i] == components[j] ==> inSameSCC(i,j))));
      @ requires (\forall int i; 0 <= i < components.length; !(\exists int j; 0 <= j < components.length; components[i] != -1 && components[i] != components[j] && inSameSCC(i, j)));
      @ ensures (\forall int i; 0 <= i < components.length; -1 <= components[i] < adjVertices.length);
      @ ensures 0 <= stackPointer <= \old(stackPointer);
      @ ensures (\forall int i; 0 <= i < dfsNumbers.length; !(onStack[i] == 1 || components[i] != -1) <==> dfsNumbers[i] == -1);
      @ // stack still remains sorted after dfsNumber
      @ ensures (\forall int i; 0 <= i < stackPointer; (\forall int j; i < j < stackPointer; (i < j) <==> (dfsNumbers[stack[i]] < dfsNumbers[stack[j]])));
      @
      @ ensures (\forall int i; 0 <= i < components.length; (\forall int j; 0 <= j < components.length; components[i] == -1 || (components[i] == components[j] ==> inSameSCC(i,j))));
      @ ensures (\forall int i; 0 <= i < components.length; !(\exists int j; 0 <= j < components.length; components[i] != -1 && components[i] != components[j] && inSameSCC(i, j)));
      @ // more stack invariants
      @ ensures (\forall int i; 0 <= i < stackPointer; stack[i] < dfsNumbers.length);
      @ // distinct elements on stack till stackPointer
      @ ensures (\forall int i; 0 <= i < stackPointer; (\forall int j; 0 <= j < stackPointer; (i != j) ==> (stack[i] != stack[j]) ));
      @ // stack sorted after dfsNumber
      @ ensures (\forall int i; 0 <= i < stackPointer; (\forall int j; i < j < stackPointer; (i < j) <==> (dfsNumbers[stack[i]] < dfsNumbers[stack[j]])));
      @ // all vertices with assigned components have no reachable non-visited vertex
      @ ensures (\forall int i; 0 <= i < components.length; (components[i] != -1) ==> (\forall int j; 0 <= j < adjVertices[i].length; (onStack[adjVertices[i][j]] == 1)|| components[adjVertices[i][j]] != -1));
      @
      @ // on stack means no component yet!
      @ ensures (\forall int i; 0 <= i < components.length; onStack[i] == 1 ==> components[i] == -1);
      @ // stack - onStack relation
      @ ensures (\forall int i; 0 <= i < onStack.length; (onStack[i] == 1) <==> (\exists int k; 0 <= k < stackPointer; stack[k] == i));
      @ // on stack only 0 or 1
      @ ensures (\forall int i; 0 <= i < onStack.length; onStack[i] == 0 || onStack[i] == 1);
      @ // vertexLabel is reachable from all stackElements
      @ ensures (\forall int i; 0 <= i < stackPointer; reachable(stack[i], vertexLabel));
      @ // for every vertex on stack there is a reachable vertex with low == dfs
      @ ensures (\forall int i; 0 <= i < stackPointer; (\exists int j; 0 <= j < stackPointer ;reachable(stack[i], stack[j]) && lowlinkNumbers[stack[j]] == dfsNumbers[stack[j]]));
      @ // assigned vertex is NOT on stack
      @ assignable components[*], onStack[*];
      @ assignable stackPointer, currentComp;
      @*/
    public void postDFS(int vertexLabel) {
        if (dfsNumbers[vertexLabel] == lowlinkNumbers[vertexLabel]) {
            while (stackPointer != 0 && dfsNumbers[stack[stackPointer - 1]] >= dfsNumbers[vertexLabel]) {
                stackPointer -= 1;
                this.components[stack[stackPointer]] = currentComp;
                onStack[stack[stackPointer]] = 0;
            }
            currentComp++;
        }

    }

}
