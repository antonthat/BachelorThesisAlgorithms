import java.util.Random;

public class TarjansAlgorithmList {
    class LinkedList {
        Node head = null;
        int size = 0;

        class Node {
            int value;
            Node next;

            Node(int value) {
                this.value = value;
            }
        }

        public void insert(int value) {
            Node newNode = new Node(value);

            if (head == null) {
                head = newNode;
            }
            else {
                Node last = head;
                while (last.next != null) {
                    last = last.next;
                }
                last.next = newNode;
            }
            size++;
        }

        public int get(int i) {
            Node resultNode = head;
            for (int k = 0; k < i; k++) {
                resultNode = resultNode.next;
            }
            return resultNode.value;
        }

        public int size() {
            return size;
        }
    }



    public int GRAPH_SIZE;
    public LinkedList[] graph;
    int currentDFSNumber;
    public int[] dfsNumbers;
    public int[] lowlinkNumbers;
    public boolean onStack[];
    public int stackPointer;
    public int[] stack;
    public int currentComponent;
    public int[] components;
    public boolean[][] reachMatrix;


    public void floydWarshall() {
        // copy direct reachable nodes from graph
        for (int i = 0; i < GRAPH_SIZE; i++) {
            for (int j = 0; j < graph[i].size(); j++) {
                reachMatrix[i][graph[i].get(j)] = true;
            }
        }

        // calculate reach matrix
        for (int k = 0; k < GRAPH_SIZE; k++) {
            for (int i = 0; i < GRAPH_SIZE; i++) {
                for (int j = 0; j < GRAPH_SIZE; j++) {
                    if (reachMatrix[i][k] && reachMatrix[k][j])
                        reachMatrix[i][j] = true;
                }
            }
        }
    }


    private int nondetInt() {
        return (new Random()).nextInt(GRAPH_SIZE);
    }

    /*@ normal_behaviour
      @ ensures (\forall int i; 0 <= i < GRAPH_SIZE; components[i] != -1);
      @ ensures (\forall int i; 0 <= i < GRAPH_SIZE;
      @             (\forall int j; i < j < GRAPH_SIZE; components[i] == components[j] ==> (reachMatrix[i][j] && reachMatrix[j][i])) &&
      @             !(\exists int j; i < j < GRAPH_SIZE; components[i] != components[j] && reachMatrix[i][j] && reachMatrix[j][i])
      @         );
      @*/
    public void startTarjans() {
        GRAPH_SIZE = 1;
        // create arrays
        graph = new LinkedList[GRAPH_SIZE];
        dfsNumbers = new int[GRAPH_SIZE];
        lowlinkNumbers = new int[GRAPH_SIZE];
        stack = new int[GRAPH_SIZE];
        onStack = new boolean[GRAPH_SIZE];
        components = new int[GRAPH_SIZE];
        reachMatrix = new boolean[GRAPH_SIZE][GRAPH_SIZE];

        // create random graph
        for (int i = 0; i < GRAPH_SIZE; i++) {
            LinkedList neighborHood = new LinkedList();

            for (int j = 0; j < GRAPH_SIZE; j++) {
                int rngB = nondetInt();
                if (rngB < 0) {
                    rngB = 0;
                }
                if (rngB >= GRAPH_SIZE) {
                    rngB = GRAPH_SIZE - 1;
                }
                neighborHood.insert(rngB);
            }
            graph[i] = neighborHood;

            dfsNumbers[i] = -1;
            lowlinkNumbers[i] = -1;
            components[i] = -1;
        }

        stackPointer = 0;
        currentDFSNumber = 0;
        currentComponent = 0;

        floydWarshall();

        for (int i = 0; i < dfsNumbers.length; i++) {
            if (dfsNumbers[i] == -1) {
                this.dfs(i);
            }
        }
    }

    public void preDFS(int vertexLabel) {
        // pre process
        dfsNumbers[vertexLabel] = currentDFSNumber;
        lowlinkNumbers[vertexLabel] = currentDFSNumber;
        currentDFSNumber++;

        stack[stackPointer] = vertexLabel;
        onStack[vertexLabel] = true;
        stackPointer++;
    }

    public void postDFS(int vertexLabel) {
        if (dfsNumbers[vertexLabel] == lowlinkNumbers[vertexLabel]) {
            while (stackPointer != 0 && dfsNumbers[stack[stackPointer - 1]] >= dfsNumbers[vertexLabel]) {
                stackPointer -= 1;
                this.components[stack[stackPointer]] = currentComponent;
                onStack[stack[stackPointer]] = false;
            }
            currentComponent++;
        }

    }

    public void dfs(int vertexLabel) {
        preDFS(vertexLabel);

        LinkedList neighborHood = graph[vertexLabel];
        for (int i = 0; i < neighborHood.size; i++) {
            int neighborVertexInd = neighborHood.get(i);
            if (dfsNumbers[neighborVertexInd] == -1) {
                dfs(neighborVertexInd);
                lowlinkNumbers[vertexLabel] = lowlinkNumbers[vertexLabel] <= lowlinkNumbers[neighborVertexInd] ? lowlinkNumbers[vertexLabel] : lowlinkNumbers[neighborVertexInd];
            } else if (dfsNumbers[neighborVertexInd] < dfsNumbers[vertexLabel] && onStack[neighborVertexInd]) {
                lowlinkNumbers[vertexLabel] = lowlinkNumbers[vertexLabel] <= dfsNumbers[neighborVertexInd] ? lowlinkNumbers[vertexLabel] : dfsNumbers[neighborVertexInd];
            }
        }

        postDFS(vertexLabel);
    }


}
