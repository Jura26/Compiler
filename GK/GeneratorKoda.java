package GK;

import java.io.BufferedReader;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.InputStreamReader;
import java.util.*;

public class GeneratorKoda {
    static int loopDepth = 0;
    static int nodeId = 0;
    static int scopeNodeId = 0;
    static HashSet<String> definedFunctions = new HashSet<>();
    static Map<String, Type> allDeclaredFunctions = new HashMap<>();
    static Map<String, List<Type>> allDefinedFunctions = new HashMap<>();
    static Stack<Type> functionStack = new Stack<>();
    static Stack<Integer> breakStack = new Stack<>();
    static Stack<Integer> continueStack = new Stack<>();
    static String currentFunctionName = "";
    static int currentStackOffset = 0;

    static java.io.ByteArrayOutputStream funcBuffer = new java.io.ByteArrayOutputStream();
    static PrintStream mainOut;
    static PrintStream funcOut = new PrintStream(funcBuffer);

    // nodes used to analyze input
    static class Node {
        int id;
        String label;
        List<Node> children = new ArrayList<>();
        // expression attributes
        Type type;
        Type itype; // inherited type - type of parent
        boolean lvalue;
        List<Type> types = null; // lista tipova argumenata (za <lista_argumenata>)
        List<String> lexValues = null;
        boolean alreadyOpenedScope = false;
        boolean loadAddress = false;
        boolean isGlobal = false;

        // variables important for output
        int row = -1;
        String lexValue = null;


        public Node() {
            this.id = nodeId++;
        }
    }

    static class scopeNode {
        int id;
        HashSet<Symbol> localVariables = new HashSet<>();
        scopeNode parent;
        int stackSize = 0;

        public scopeNode(scopeNode parent) {
            this.id = scopeNodeId++;
            this.parent = parent;
        }

    }

    static class Type {
        enum Basic {INT, CHAR, VOID};

        Basic basic;
        boolean isSequence = false;
        boolean isConst = false;
        boolean isFunction = false;
        boolean isStringLiteral;
        Type returnType = null;  // povratni tip funkcije (pov)
        List<Type> paramTypes = null;  // tipovi parametara funkcije (params)
        Integer elemNr = null;

        Type(Basic basic) {
            this.basic = basic;
        }
        Type(Type t){
            this.basic = t.basic;
            this.isSequence = t.isSequence;
            this.isConst = t.isConst;
            this.isFunction = t.isFunction;
            this.returnType = t.returnType;
            this.paramTypes = t.paramTypes;
            this.elemNr = t.elemNr;
            this.isStringLiteral = t.isStringLiteral;
        }
    }

    static class Symbol {
        String lexValue;

        // expression attributes
        Type type;
        String label;
        Type itype; // inherited type - type of parent
        boolean lvalue;
        int offset;

        Symbol(String name, Type type) {
            this.lexValue = name;
            this.type = type;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Symbol)) return false;
            Symbol s = (Symbol) o;
            return Objects.equals(this.lexValue, s.lexValue);
        }

        @Override
        public int hashCode() {
            return Objects.hash(lexValue);
        }
        @Override
        public String toString() {
            return lexValue + " " + label;
        }
    }

    private static int depth(String line){
        int i = 0;
        while (i < line.length() && line.charAt(i) == ' ') i++;
        return i;
    }

    private static Node parseLine(String line){
        line =  line.trim();
        String[] parts = line.split(" ");

        Node node = new Node();
        node.label = parts[0];

        // if row contains terminated
        if (!parts[0].startsWith("<")){
            // epsilon row (empty)
            if (parts[0].equals("$")) return node;

            // row number is the second part of the line
            node.row = Integer.parseInt(parts[1]);

            // lexvalue is the rest of the line
            StringBuilder sb = new StringBuilder();
            for (int i = 2; i < parts.length; i++){
                sb.append(parts[i]);
                if (i < parts.length-1) sb.append(" ");
            }
            node.lexValue = sb.toString();
        }

        return node;
    }

    // parse tree from sintax analysis output
    private static Node loadTree() throws IOException{
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        String line;
        Stack<Node> stack= new Stack<>();
        Node root = null;

        while ((line = br.readLine()) != null) {
            if (line.isEmpty()) continue;

            int d = depth(line);
            Node node = parseLine(line);

            // get to the right level (depth)
            while (stack.size() > d){
                stack.pop();
            }

            if (stack.isEmpty()){
                // node becomes the root
                root = node;
            }else{
                // node becomes a child of the last node on the stack
                stack.peek().children.add(node);
            }
            stack.push(node);

        }

        return root;
    }

    static Stack<scopeNode> scopeStack = new Stack<>();

    // creating a new scope
    private static scopeNode newScope() {
        scopeNode parent = null;
        if (!scopeStack.isEmpty()){
            parent = scopeStack.peek();
        }
        scopeNode ns = new scopeNode(parent);
        scopeStack.push(ns);
        return ns;
    }

    static boolean canAssign(Type from, Type to) {
        if (from == null || to == null)
            return false;

        if (from.isSequence || to.isSequence) {

            if (!from.isSequence || !to.isSequence)
                return false;

            if (from.basic != to.basic)
                return false;

            if (!from.isConst && !to.isConst)
                return true;

            if (from.isConst && to.isConst)
                return true;

            if (!from.isConst && to.isConst)
                return true;

            return false;
        }

        if (from.basic == to.basic)
            return true;

        if (from.basic == Type.Basic.CHAR && to.basic == Type.Basic.INT)
            return true;

        return false;
    }

    static boolean canExplicitAssign(Type from, Type to) {
        if(canAssign(from, to))
            return true;
        return from.basic == Type.Basic.INT && to.basic == Type.Basic.CHAR;
    }

    static boolean isSameFunction(Type t1, Type t2) {

        if (!t1.isFunction || !t2.isFunction) return false;

        if (t1.returnType.basic != t2.returnType.basic) return false;

        if (t1.paramTypes.size() != t2.paramTypes.size()) return false;

        for (int i = 0; i < t1.paramTypes.size(); i++) {
            Type p1 = t1.paramTypes.get(i);
            Type p2 = t2.paramTypes.get(i);

            if (p1.basic != p2.basic || p1.isSequence != p2.isSequence) {
                return false;
            }
        }

        return true;
    }

    static void process(Node node) {
        switch (node.label) {
            case "<primarni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("IDN")) {
                    boolean found = false;
                    Symbol sFound = null;
                    scopeNode curr = scopeStack.peek();

                    while (!found && curr != null) {

                        for (Symbol s : curr.localVariables) {
                            if (s.lexValue.equals(node.children.get(0).lexValue)) {
                                found = true;
                                sFound = s;
                                node.type = s.type;
                                node.lvalue = s.lvalue;
                            }
                        }
                        curr = curr.parent;
                    }

                    if (!found) {
                        err(node);
                    }

                    if (curr == scopeStack.firstElement()) {
                         node.isGlobal = true;
                         System.out.println("    LDR R0, =G_" + sFound.lexValue);
                         if (!node.loadAddress && !sFound.type.isSequence) {
                             System.out.println("    LDR R0, [R0]");
                         }
                         System.out.println("    PUSH {R0}");
                         currentStackOffset += 4;
                    } else {
                        int dist = currentStackOffset - sFound.offset - 4;
                        if (node.loadAddress || sFound.type.isSequence) {
                            System.out.println("    ADD R0, SP, #" + dist);
                        } else {
                            System.out.println("    LDR R0, [SP, #" + dist + "]");
                        }
                        System.out.println("    PUSH {R0}");
                        currentStackOffset += 4;
                    }

                } else if (node.children.size() == 1 && node.children.get(0).label.equals("BROJ")) {
                    try {
                        long br = Long.parseLong(node.children.get(0).lexValue);
                        if (br < Integer.MIN_VALUE || br > Integer.MAX_VALUE) {
                            err(node);
                        }
                        node.type = new Type(Type.Basic.INT);
                        node.lvalue = false;
                    } catch (NumberFormatException nfe){
                        err(node);
                    }
                    System.out.println("    LDR R0, =" + node.children.get(0).lexValue);
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                } else if (node.children.size() == 1 && node.children.get(0).label.equals("ZNAK")) {
                    node.type = new Type(Type.Basic.CHAR);
                    node.lvalue = false;
                } else if (node.children.size() == 1 && node.children.get(0).label.equals("NIZ_ZNAKOVA")) {
                    String s = node.children.get(0).lexValue;
                    for (int i = 1; i < s.length() - 1; i++) {
                        if (s.charAt(i) == '\\') {
                            if (i + 1 >= s.length() - 1) {
                                err(node);
                            }

                            char sljedeci = s.charAt(i + 1);
                            if (sljedeci != 'n' && sljedeci != 't' && sljedeci != '0' &&
                                    sljedeci != '\'' && sljedeci != '\"' && sljedeci != '\\') {
                                err(node);
                            }
                            i++;
                        }
                    }
                    node.type = new Type(Type.Basic.CHAR);
                    node.type.isSequence = true;
                    node.type.isConst = true;
                    node.type.elemNr = node.children.get(0).lexValue.length() - 2 + 1;
                    node.type.isStringLiteral = true;
                    node.lvalue = false;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("L_ZAGRADA") && node.children.get(1).label.equals("<izraz>") && node.children.get(2).label.equals("D_ZAGRADA")) {
                    process(node.children.get(1));
                    node.type = new Type(node.children.get(1).type);
                    node.lvalue = node.children.get(1).lvalue;
                }
                break;

            case "<postfiks_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<primarni_izraz>")) {
                    Node prim = node.children.get(0);
                    prim.loadAddress = node.loadAddress;
                    process(prim);
                    node.type = new Type(prim.type);
                    node.lvalue = prim.lvalue;
                    node.isGlobal = prim.isGlobal;
                } else if (node.children.size() == 4 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_UGL_ZAGRADA") && node.children.get(2).label.equals("<izraz>") && node.children.get(3).label.equals("D_UGL_ZAGRADA")) {

                    Node postfiks = node.children.get(0);
                    Node izraz = node.children.get(2);

                    postfiks.loadAddress = true;
                    process(postfiks);
                    node.isGlobal = postfiks.isGlobal;
                    process(izraz);

                    if (postfiks.type == null || !postfiks.type.isSequence) {
                        err(node);
                    }

                    Type elementType = new Type(postfiks.type.basic);
                    elementType.isSequence = false;
                    elementType.isConst = postfiks.type.isConst;
                    node.type = elementType;

                    node.lvalue = !elementType.isConst;

                    Type intType = new Type(Type.Basic.INT);
                    if (izraz.type == null || !canAssign(izraz.type, intType)) {
                        err(node);
                    }

                    System.out.println("    POP {R1}");
                    System.out.println("    POP {R0}");
                    System.out.println("    LSL R1, R1, #2");
                    if (postfiks.isGlobal) {
                        System.out.println("    ADD R0, R0, R1");
                    } else {
                        System.out.println("    SUB R0, R0, R1");
                    }
                    
                    if (!node.loadAddress) {
                        System.out.println("    LDR R0, [R0]");
                    }
                    System.out.println("    PUSH {R0}");
                    currentStackOffset -= 4;

                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("D_ZAGRADA")) {

                    Node postfiks = node.children.get(0);
                    // Manually resove function name to avoid loading it
                    Node curr = postfiks;
                    while(curr.children.size() == 1 && !curr.children.get(0).label.equals("IDN") && curr.children.get(0).label.startsWith("<")) {
                        curr = curr.children.get(0);
                    }
                    if (curr.children.size() != 1 || !curr.children.get(0).label.equals("IDN")) err(node);
                    String funcName = curr.children.get(0).lexValue;

                    Symbol funcSym = null;
                    scopeNode globalScope = scopeStack.firstElement();
                    for(Symbol s : globalScope.localVariables) {
                        if(s.lexValue.equals(funcName) && s.type.isFunction) {
                            funcSym = s;
                            break;
                        }
                    }
                    if (funcSym == null) err(node);
                    postfiks.type = funcSym.type;

                    if (postfiks.type.isFunction) {
                        boolean noParameters = postfiks.type.paramTypes.isEmpty() ||
                                (postfiks.type.paramTypes.size() == 1 && postfiks.type.paramTypes.get(0).basic == Type.Basic.VOID);

                        if (!noParameters) {
                            err(node);
                        }
                    } else err(node);

                    node.type = new Type(postfiks.type.returnType);
                    node.lvalue = false;

                    System.out.println("    BL F_" + funcName.toUpperCase());
                    System.out.println("    PUSH {R6}");
                    currentStackOffset += 4;

                } else if (node.children.size() == 4 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<lista_argumenata>") && node.children.get(3).label.equals("D_ZAGRADA")) {

                    Node postfiks = node.children.get(0);
                    Node listaArgumenata = node.children.get(2);

                    Node curr = postfiks;
                    while(curr.children.size() == 1 && !curr.children.get(0).label.equals("IDN") && curr.children.get(0).label.startsWith("<")) {
                        curr = curr.children.get(0);
                    }
                    if (curr.children.size() != 1 || !curr.children.get(0).label.equals("IDN")) err(node);
                    String funcName = curr.children.get(0).lexValue;

                    Symbol funcSym = null;
                    scopeNode globalScope = scopeStack.firstElement();
                    for(Symbol s : globalScope.localVariables) {
                        if(s.lexValue.equals(funcName) && s.type.isFunction) {
                            funcSym = s;
                            break;
                        }
                    }
                    if (funcSym == null) err(node);
                    postfiks.type = funcSym.type;

                    process(listaArgumenata);

                    if (postfiks.type == null || !postfiks.type.isFunction) {
                        err(node);
                    }

                    if (postfiks.type.paramTypes == null || listaArgumenata.types == null ||
                            postfiks.type.paramTypes.size() != listaArgumenata.types.size()) {
                        err(node);
                    }

                    for (int i = 0; i < postfiks.type.paramTypes.size(); i++) {
                        Type argType = listaArgumenata.types.get(i);
                        Type paramType = postfiks.type.paramTypes.get(i);

                        if (!canAssign(argType, paramType)) {
                            err(node);
                        }
                    }

                    node.type = new Type(postfiks.type.returnType);
                    node.lvalue = false;
                    
                    System.out.println("    BL F_" + funcName.toUpperCase());
                    int argSize = listaArgumenata.types.size() * 4;
                    System.out.println("    ADD SP, SP, #" + argSize);
                    currentStackOffset -= argSize; 
                    
                    System.out.println("    PUSH {R6}");
                    currentStackOffset += 4;

                } else if (node.children.size() == 2 &&
                        node.children.get(0).label.equals("<postfiks_izraz>") &&
                        (node.children.get(1).label.equals("OP_INC") ||
                                node.children.get(1).label.equals("OP_DEC"))) {

                    Node postfiks = node.children.get(0);
                    postfiks.loadAddress = true;
                    process(postfiks);
                    if (!postfiks.lvalue || !canAssign(postfiks.type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                    
                    System.out.println("    POP {R1}");
                    System.out.println("    LDR R0, [R1]");
                    System.out.println("    PUSH {R0}"); // Result
                    if (node.children.get(1).label.equals("OP_INC")) {
                        System.out.println("    ADD R0, R0, #1");
                    } else {
                        System.out.println("    SUB R0, R0, #1");
                    }
                    System.out.println("    STR R0, [R1]");
                    currentStackOffset -= 4; // POP R1 (-4). PUSH R0 (+4). Need to account for POP. Wait.
                    // Process -> +4.
                    // POP R1 -> -4. Stack +0 relative to start.
                    // PUSH R0 -> +4. Stack +4 relative to start.
                    // currentStackOffset is updated by process (+4).
                    // I emit POP. currentStackOffset -= 4.
                    // I emit PUSH. currentStackOffset += 4.
                    // Net change 0.
                    // The 'currentStackOffset -= 4' in my last edit was for the Array case (which popped 2, pushed 1).
                    // This case pops 1 (Addr), pushes 1 (Val).
                    // Wait. `process(postfiks)` pushed Address (+4).
                    // `POP {R1}` (-4).
                    // `PUSH {R0}` (+4).
                    // So net is +4.
                    // process already added 4.
                    // So I just need to decrement for the POP and increment for PUSH.
                    // So net 0 adjustment?
                    // Yes. No 'currentStackOffset -= 4' here is needed?
                    // Ah, process() adds 4.
                    // I want final state to be +4.
                    // It IS +4 (from process).
                    // But I did POP/PUSH manually.
                    // My manual changes to stack pointer MUST be reflected in `currentStackOffset`.
                    // offset = offset - 4 + 4.
                    // So NO change to `currentStackOffset` needed? Same value.
                    // Valid coding checks:
                    // offset starts at X.
                    // process(postfiks): offset = X+4.
                    // POP: offset = X.
                    // PUSH: offset = X+4.
                    // So `currentStackOffset` logic in code?
                    // Code variable `currentStackOffset` holds the X+4 value.
                    // I need it to hold X+4 value.
                    // So I do nothing.
                }
                break;

            case "<lista_argumenata>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<izraz_pridruzivanja>")) {
                    process(node.children.get(0));
                    node.types = new ArrayList<>();
                    node.types.add(node.children.get(0).type);
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<lista_argumenata>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<izraz_pridruzivanja>")) {

                    process(node.children.get(0));
                    process(node.children.get(2));

                    node.types = new ArrayList<>();
                    node.types.addAll(node.children.get(0).types);
                    node.types.add(node.children.get(2).type);
                }
                break;

            case "<unarni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<postfiks_izraz>")) {
                    Node child = node.children.get(0);
                    child.loadAddress = node.loadAddress; // Pass requirement
                    process(child);
                    node.type = child.type;
                    node.lvalue = child.lvalue;
                }
                else if (node.children.size() == 2 && (node.children.get(0).label.equals("OP_INC") || node.children.get(0).label.equals("OP_DEC")) && node.children.get(1).label.equals("<unarni_izraz>")) {

                    Node child = node.children.get(1);
                    child.loadAddress = true;
                    process(child);
                    if (!child.lvalue || !canAssign(child.type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                    
                    System.out.println("    POP {R1}");
                    System.out.println("    LDR R0, [R1]");
                    if (node.children.get(0).label.equals("OP_INC")) {
                        System.out.println("    ADD R0, R0, #1");
                    } else {
                        System.out.println("    SUB R0, R0, #1");
                    }
                    System.out.println("    STR R0, [R1]");
                    System.out.println("    PUSH {R0}");
                }
                else if (node.children.size() == 2 && node.children.get(0).label.equals("<unarni_operator>") && node.children.get(1).label.equals("<cast_izraz>")) {

                    process(node.children.get(1));
                    if (!canAssign(node.children.get(1).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    String operator = node.children.get(0).children.get(0).label;
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    if (operator.equals("MINUS")) {
                        System.out.println("    NEG R0, R0");
                    } else if (operator.equals("OP_NEG")) {
                        System.out.println("    CMP R0, #0");
                        System.out.println("    MOVEQ R0, #1");
                        System.out.println("    MOVNE R0, #0");
                    } else if (operator.equals("OP_TILDA")) {
                        System.out.println("    MVN R0, R0");
                    }
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<unarni_operator>":
                break;

            case "<cast_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<unarni_izraz>")) {

                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 4 && node.children.get(0).label.equals("L_ZAGRADA") && node.children.get(1).label.equals("<ime_tipa>") && node.children.get(2).label.equals("D_ZAGRADA") && node.children.get(3).label.equals("<cast_izraz>")) {

                    Node typeName = node.children.get(1);
                    Node castExp = node.children.get(3);

                    process(typeName);
                    process(castExp);

                    if (!canExplicitAssign(castExp.type, typeName.type)) {
                        err(node);
                    }

                    if (node.children.get(3).type.isFunction || node.children.get(3).type.isSequence) {
                        err(node);
                    }

                    node.type = typeName.type;
                    node.lvalue = false;
                }
                break;

            case "<ime_tipa>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<specifikator_tipa>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                } else if (node.children.size() == 2 && node.children.get(0).label.equals("KR_CONST") && node.children.get(1).label.equals("<specifikator_tipa>")) {

                    Node spec = node.children.get(1);
                    process(spec);
                    if (spec.type.basic == Type.Basic.VOID) {
                        err(node);
                    }
                    node.type = new Type(spec.type);
                    node.type.isConst = true;
                }
                break;

            case "<specifikator_tipa>":
                if (node.children.size() == 1)
                    if (node.children.get(0).label.equals("KR_VOID")){
                        node.type = new Type(Type.Basic.VOID);
                    }
                    else if (node.children.get(0).label.equals("KR_INT")) {
                        node.type = new Type(Type.Basic.INT);
                    }
                    else if (node.children.get(0).label.equals("KR_CHAR")) {
                        node.type = new Type(Type.Basic.CHAR);
                    }
                    else {
                        err(node);
                    }
                break;

            case "<multiplikativni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<cast_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 &&
                        node.children.get(0).label.equals("<multiplikativni_izraz>") &&
                        (node.children.get(1).label.equals("OP_PUTA") ||
                                node.children.get(1).label.equals("OP_DIJELI") ||
                                node.children.get(1).label.equals("OP_MOD")) &&
                        node.children.get(2).label.equals("<cast_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;

                    System.out.println("    POP {R1}");
                    currentStackOffset -= 4;
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    if (node.children.get(1).label.equals("OP_PUTA")) {
                         System.out.println("    MUL R0, R0, R1");
                    } else if (node.children.get(1).label.equals("OP_DIJELI")) {
                         System.out.println("    BL DO_DIV"); // R0 = R0 / R1
                    } else if (node.children.get(1).label.equals("OP_MOD")) {
                         System.out.println("    BL DO_MOD"); // R0 = R0 % R1
                    }
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                }
                break;

            case "<aditivni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<multiplikativni_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 &&
                        node.children.get(0).label.equals("<aditivni_izraz>") &&
                        (node.children.get(1).label.equals("PLUS") ||
                                node.children.get(1).label.equals("MINUS")) &&
                        node.children.get(2).label.equals("<multiplikativni_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                    System.out.println("    POP {R1}");
                    currentStackOffset -= 4;
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    if (node.children.get(1).label.equals("PLUS")) {
                        System.out.println("    ADD R0, R0, R1");
                    } else {
                        System.out.println("    SUB R0, R0, R1");
                    }
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                }
                break;

            case "<odnosni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<aditivni_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 &&
                        node.children.get(0).label.equals("<odnosni_izraz>") &&
                        (node.children.get(1).label.equals("OP_LT") ||
                                node.children.get(1).label.equals("OP_GT") ||
                                node.children.get(1).label.equals("OP_LTE") ||
                                node.children.get(1).label.equals("OP_GTE")) &&
                        node.children.get(2).label.equals("<aditivni_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                    System.out.println("    POP {R1}");
                    currentStackOffset -= 4;
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    CMP R0, R1");
                    String op = node.children.get(1).label;
                    if (op.equals("OP_LT")) {
                         System.out.println("    MOVLT R0, #1");
                         System.out.println("    MOVGE R0, #0");
                    } else if (op.equals("OP_GT")) {
                         System.out.println("    MOVGT R0, #1");
                         System.out.println("    MOVLE R0, #0");
                    } else if (op.equals("OP_LTE")) {
                         System.out.println("    MOVLE R0, #1");
                         System.out.println("    MOVGT R0, #0");
                    } else if (op.equals("OP_GTE")) {
                         System.out.println("    MOVGE R0, #1");
                         System.out.println("    MOVLT R0, #0");
                    }
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                }
                break;

            case "<jednakosni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<odnosni_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<jednakosni_izraz>") && (node.children.get(1).label.equals("OP_EQ") || node.children.get(1).label.equals("OP_NE")) && node.children.get(2).label.equals("<odnosni_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    if (node.children.get(0).type.isFunction || node.children.get(2).type.isFunction
                        || node.children.get(0).type.isSequence || node.children.get(2).type.isSequence) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                    System.out.println("    POP {R1}");
                    currentStackOffset -= 4;
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    CMP R0, R1");
                    if (node.children.get(1).label.equals("OP_EQ")) {
                        System.out.println("    MOVEQ R0, #1");
                        System.out.println("    MOVNE R0, #0");
                    } else {
                        System.out.println("    MOVNE R0, #1");
                        System.out.println("    MOVEQ R0, #0");
                    }
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                }
                break;

            case "<bin_i_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<jednakosni_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<bin_i_izraz>") && node.children.get(1).label.equals("OP_BIN_I") && node.children.get(2).label.equals("<jednakosni_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                    System.out.println("    POP {R1}");
                    currentStackOffset -= 4;
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    AND R0, R0, R1");
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                } else {
                    err(node);
                }
                break;

            case "<bin_xili_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<bin_i_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<bin_xili_izraz>") && node.children.get(1).label.equals("OP_BIN_XILI") && node.children.get(2).label.equals("<bin_i_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                    System.out.println("    POP {R1}");
                    currentStackOffset -= 4;
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    EOR R0, R0, R1");
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                } else {
                    err(node);
                }
                break;

            case "<bin_ili_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<bin_xili_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<bin_ili_izraz>") && node.children.get(1).label.equals("OP_BIN_ILI") && node.children.get(2).label.equals("<bin_xili_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                    System.out.println("    POP {R1}");
                    currentStackOffset -= 4;
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    ORR R0, R0, R1");
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                } else {
                    err(node);
                }
                break;

            case "<log_i_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<bin_ili_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<log_i_izraz>") && node.children.get(1).label.equals("OP_I") && node.children.get(2).label.equals("<bin_ili_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    int labelFalse = node.id; // Unique ID
                    int labelEnd = node.id + 1000000;
                    // Eval A
                    System.out.println("    POP {R0}"); // Result of A
                    currentStackOffset -= 4;
                    System.out.println("    CMP R0, #0");
                    System.out.println("    BEQ L_FALSE_" + labelFalse);
                    
                    process(node.children.get(2)); // Eval B
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    System.out.println("    POP {R0}"); // Result of B
                    currentStackOffset -= 4;
                    System.out.println("    CMP R0, #0");
                    System.out.println("    BEQ L_FALSE_" + labelFalse);
                    System.out.println("    MOV R0, #1");
                    System.out.println("    B L_END_" + labelFalse);
                    System.out.println("L_FALSE_" + labelFalse + ":");
                    System.out.println("    MOV R0, #0");
                    System.out.println("L_END_" + labelFalse + ":");
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    err(node);
                }
                break;

            case "<log_ili_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<log_i_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<log_ili_izraz>") && node.children.get(1).label.equals("OP_ILI") && node.children.get(2).label.equals("<log_i_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    int labelTrue = node.id;
                    // Eval A
                    System.out.println("    POP {R0}"); // Result of A
                    currentStackOffset -= 4;
                    System.out.println("    CMP R0, #0");
                    System.out.println("    BNE L_TRUE_" + labelTrue);
                    
                    process(node.children.get(2)); // Eval B
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    CMP R0, #0");
                    System.out.println("    BNE L_TRUE_" + labelTrue);
                    System.out.println("    MOV R0, #0");
                    System.out.println("    B L_END_" + labelTrue);
                    System.out.println("L_TRUE_" + labelTrue + ":");
                    System.out.println("    MOV R0, #1");
                    System.out.println("L_END_" + labelTrue + ":");
                    System.out.println("    PUSH {R0}");
                    currentStackOffset += 4;
                    
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    err(node);
                }
                break;

            case "<izraz_pridruzivanja>":
                if (node.children.size() == 1) {
                    Node e = node.children.get(0);
                    process(e);
                    node.type = new Type(e.type);
                    node.lvalue = e.lvalue;
                } else {
                    Node postfiks = node.children.get(0);
                    Node izraz = node.children.get(2);

                    postfiks.loadAddress = true;
                    process(postfiks);
                    process(izraz);

                    if (!postfiks.lvalue || postfiks.type.isConst) {
                        err(node);
                    }
                    if (izraz.type == null || !canAssign(izraz.type, postfiks.type)) {
                        err(node);
                    }

                    System.out.println("    POP {R0}");
                    System.out.println("    POP {R1}");
                    System.out.println("    STR R0, [R1]");
                    System.out.println("    PUSH {R0}");
                    currentStackOffset -= 4;

                    node.type = new Type(postfiks.type);
                    node.lvalue = false;
                }
                break;

            case "<izraz>":
                if (node.children.size() == 1) {
                    if (node.children.get(0).label.equals("<izraz_pridruzivanja>")) {
                        Node izraz_pri = node.children.get(0);
                        process(izraz_pri);
                        node.type = new Type(izraz_pri.type);
                        node.lvalue = izraz_pri.lvalue;
                    } else {
                        err(node);
                    }
                } else if (node.children.size() == 3) {
                    if (node.children.get(0).label.equals("<izraz>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<izraz_pridruzivanja>")) {
                        Node izraz_pri = node.children.get(2);
                        process(node.children.get(0));
                        process(izraz_pri);
                        node.type = new Type(izraz_pri.type);
                        node.lvalue = false;
                    } else {
                        err(node);
                    }
                } else {
                    err(node);
                }
                break;

            // control structure

            case "<slozena_naredba>":
                int offsetBefore = currentStackOffset;
                boolean weOpened = false;
                if (!node.alreadyOpenedScope) {
                    newScope();
                    weOpened = true;
                }
                if (node.children.size() == 3 &&
                        node.children.get(0).label.equals("L_VIT_ZAGRADA") &&
                        node.children.get(1).label.equals("<lista_naredbi>") &&
                        node.children.get(2).label.equals("D_VIT_ZAGRADA")) {
                    newScope();
                    process(node.children.get(1));
                    int taken = currentStackOffset - offsetBefore;
                    if (taken > 0) {
                        System.out.println("    ADD SP, SP, #" + taken);
                        currentStackOffset = offsetBefore;
                    }
                    scopeStack.pop();
                } else if (node.children.size() == 4 &&
                        node.children.get(0).label.equals("L_VIT_ZAGRADA") &&
                        node.children.get(1).label.equals("<lista_deklaracija>") &&
                        node.children.get(2).label.equals("<lista_naredbi>") &&
                        node.children.get(3).label.equals("D_VIT_ZAGRADA")) {
                    newScope();
                    process(node.children.get(1));
                    process(node.children.get(2));
                    int taken = currentStackOffset - offsetBefore;
                    if (taken > 0) {
                        System.out.println("    ADD SP, SP, #" + taken);
                        currentStackOffset = offsetBefore;
                    }
                    scopeStack.pop();
                }
                break;

            case "<lista_naredbi>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<naredba>")) {
                    process(node.children.get(0));
                } else if (node.children.size() == 2 && node.children.get(0).label.equals("<lista_naredbi>") && node.children.get(1).label.equals("<naredba>")) {
                    process(node.children.get(0));
                    process(node.children.get(1));
                }
                break;

            case "<naredba>":
                if (node.children.size() == 1)
                    process(node.children.get(0));

                break;

            case "<izraz_naredba>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("TOCKAZAREZ"))
                    node.type = new Type(Type.Basic.INT);
                else if (node.children.size() == 2 && node.children.get(0).label.equals("<izraz>") && node.children.get(1).label.equals("TOCKAZAREZ")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                } else {
                    err(node);
                }
                break;

            case "<naredba_grananja>":
                if (node.children.size() == 5 &&
                        node.children.get(0).label.equals("KR_IF") &&
                        node.children.get(1).label.equals("L_ZAGRADA") &&
                        node.children.get(2).label.equals("<izraz>") &&
                        node.children.get(3).label.equals("D_ZAGRADA") &&
                        node.children.get(4).label.equals("<naredba>")) {
                    int labelElse = node.id;
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    if (node.children.get(2).type.isFunction || node.children.get(2).type.isSequence) {
                        err(node);
                    }
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    CMP R0, #0");
                    System.out.println("    BEQ L_END_" + labelElse);
                    process(node.children.get(4));
                    System.out.println("L_END_" + labelElse + ":");
                } else if (node.children.size() == 7 &&
                        node.children.get(0).label.equals("KR_IF") &&
                        node.children.get(1).label.equals("L_ZAGRADA") &&
                        node.children.get(2).label.equals("<izraz>") &&
                        node.children.get(3).label.equals("D_ZAGRADA") &&
                        node.children.get(4).label.equals("<naredba>") &&
                        node.children.get(5).label.equals("KR_ELSE") &&
                        node.children.get(6).label.equals("<naredba>")) {
                    int labelElse = node.id;
                    int labelEnd = node.id + 1000000;
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    CMP R0, #0");
                    System.out.println("    BEQ L_ELSE_" + labelElse);
                    process(node.children.get(4));
                    System.out.println("    B L_END_" + labelEnd);
                    System.out.println("L_ELSE_" + labelElse + ":");
                    process(node.children.get(6));
                    System.out.println("L_END_" + labelEnd + ":");
                }
                break;

            case "<naredba_petlje>":
                int loopId = node.id;
                int startLabel = loopId;
                int endLabel = loopId + 1000000;
                int stepLabel = loopId + 2000000;

                if (node.children.size() == 5 && node.children.get(0).label.equals("KR_WHILE") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<izraz>") && node.children.get(3).label.equals("D_ZAGRADA") && node.children.get(4).label.equals("<naredba>")) {
                    continueStack.push(startLabel);
                    breakStack.push(endLabel);
                    System.out.println("L_START_" + startLabel + ":");
                    Node izraz = node.children.get(2);
                    process(izraz);
                    if (!canAssign(izraz.type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    CMP R0, #0");
                    System.out.println("    BEQ L_END_" + endLabel);
                    loopDepth++;
                    process(node.children.get(4));
                    loopDepth--;
                    System.out.println("    B L_START_" + startLabel);
                    System.out.println("L_END_" + endLabel + ":");
                    continueStack.pop();
                    breakStack.pop();
                } else if (node.children.size() == 6 && node.children.get(0).label.equals("KR_FOR") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<izraz_naredba>") && node.children.get(3).label.equals("<izraz_naredba>") && node.children.get(4).label.equals("D_ZAGRADA") && node.children.get(5).label.equals("<naredba>")) {
                    continueStack.push(stepLabel);
                    breakStack.push(endLabel);
                    process(node.children.get(2)); // Init
                    System.out.println("L_START_" + startLabel + ":");
                    Node cond = node.children.get(3);
                    if (cond.children.size() == 2) {
                        process(cond.children.get(0));
                        if (!canAssign(cond.children.get(0).type, new Type(Type.Basic.INT))) {
                            err(node);
                        }
                        if (cond.children.get(0).type.isFunction || cond.children.get(0).type.isSequence) {
                            err(node);
                        }
                        System.out.println("    POP {R0}");
                        currentStackOffset -= 4;
                        System.out.println("    CMP R0, #0");
                        System.out.println("    BEQ L_END_" + endLabel);
                    }
                    loopDepth++;
                    process(node.children.get(5));
                    loopDepth--;
                    System.out.println("L_STEP_" + stepLabel + ":");
                    System.out.println("    B L_START_" + startLabel);
                    System.out.println("L_END_" + endLabel + ":");
                    continueStack.pop();
                    breakStack.pop();
                } else if (node.children.size() == 7 && node.children.get(0).label.equals("KR_FOR") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<izraz_naredba>") && node.children.get(3).label.equals("<izraz_naredba>") && node.children.get(4).label.equals("<izraz>") && node.children.get(5).label.equals("D_ZAGRADA") && node.children.get(6).label.equals("<naredba>")) {
                    continueStack.push(stepLabel);
                    breakStack.push(endLabel);
                    process(node.children.get(2)); // Init
                    System.out.println("L_START_" + startLabel + ":");
                    Node cond = node.children.get(3);
                    if (cond.children.size() == 2) {
                        process(cond.children.get(0));
                         if (!canAssign(cond.children.get(0).type, new Type(Type.Basic.INT))) {
                            err(node);
                        }
                        if (cond.children.get(0).type.isFunction || cond.children.get(0).type.isSequence) {
                            err(node);
                        }
                        System.out.println("    POP {R0}");
                        currentStackOffset -= 4;
                        System.out.println("    CMP R0, #0");
                        System.out.println("    BEQ L_END_" + endLabel);
                    }
                    loopDepth++;
                    process(node.children.get(6));
                    loopDepth--;
                    System.out.println("L_STEP_" + stepLabel + ":");
                    process(node.children.get(4)); // Step
                    // Step expression result needs to be discarded?
                    // Expressions push result.
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    B L_START_" + startLabel);
                    System.out.println("L_END_" + endLabel + ":");
                    continueStack.pop();
                    breakStack.pop();
                } else {
                    err(node);
                }
                break;

            case "<naredba_skoka>":
                if (node.children.size() == 2 && (node.children.get(0).label.equals("KR_CONTINUE") || node.children.get(0).label.equals("KR_BREAK")) && node.children.get(1).label.equals("TOCKAZAREZ")) {
                    if (loopDepth == 0) {
                        err(node);
                    }
                    if (node.children.get(0).label.equals("KR_BREAK")) {
                         int target = breakStack.peek();
                         System.out.println("    B L_END_" + target);
                    } else {
                         int target = continueStack.peek();
                         if (target >= 2000000) { // Step label
                             System.out.println("    B L_STEP_" + target);
                         } else {
                             System.out.println("    B L_START_" + target);
                         }
                    }
                } else if (node.children.size() == 2 && node.children.get(0).label.equals("KR_RETURN") && node.children.get(1).label.equals("TOCKAZAREZ")) {
                    Type returnType = functionStack.peek();
                    if (returnType.basic != Type.Basic.VOID) {
                        err(node);
                    }
                    System.out.println("    ADD SP, SP, #" + (currentStackOffset - 4));
                    System.out.println("    POP {PC}");
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("KR_RETURN") && node.children.get(1).label.equals("<izraz>") && node.children.get(2).label.equals("TOCKAZAREZ")) {
                    process(node.children.get(1));
                    if (!canAssign(node.children.get(1).type, functionStack.peek())) {
                        err(node);
                    }
                    System.out.println("    POP {R0}");
                    currentStackOffset -= 4;
                    System.out.println("    MOV R6, R0");
                    System.out.println("    ADD SP, SP, #" + (currentStackOffset - 4));
                    System.out.println("    POP {PC}");
                }
                break;


            case "<prijevodna_jedinica>":
                if (node.children.size() == 1) {
                    process(node.children.get(0));
                } else {
                    process(node.children.get(0));
                    process(node.children.get(1));
                }
                break;

            case "<vanjska_deklaracija>":
                if (node.children.size() == 1 && (node.children.get(0).label.equals("<deklaracija>") || node.children.get(0).label.equals("<definicija_funkcije>"))) {
                    process(node.children.get(0));
                } else {
                    err(node);
                }
                break;


            // declarations and functions

            case "<definicija_funkcije>":
                int savedOffset = currentStackOffset;
                currentStackOffset = 0; // Reset stack offset for function body
                System.setOut(funcOut);
                currentFunctionName = node.children.get(1).lexValue;
                System.out.println("F_" + currentFunctionName.toUpperCase() + ":");
                System.out.println("    PUSH {LR}");
                currentStackOffset += 4;
                if (node.children.size() == 6 &&
                        node.children.get(0).label.equals("<ime_tipa>") &&
                        node.children.get(1).label.equals("IDN") &&
                        node.children.get(2).label.equals("L_ZAGRADA") &&
                        node.children.get(3).label.equals("KR_VOID") &&
                        node.children.get(4).label.equals("D_ZAGRADA") &&
                        node.children.get(5).label.equals("<slozena_naredba>")) {

                    process(node.children.get(0));

                    if (node.children.get(0).type.isConst) {
                        err(node);
                    }

                    String funcName = node.children.get(1).lexValue;
                    Type returnType = new Type(node.children.get(0).type);

                    if (definedFunctions.contains(funcName)) {
                        err(node);
                    }

                    scopeNode globalScope = scopeStack.firstElement();
                    boolean declared = false;
                    for (Symbol s : globalScope.localVariables) {
                        if (s.lexValue.equals(funcName)) {
                            declared = true;
                            if (!s.type.isFunction ||
                                    s.type.paramTypes.size() != 1 ||
                                    s.type.paramTypes.get(0).basic != Type.Basic.VOID ||
                                    s.type.returnType.basic != returnType.basic) {
                                err(node);
                            }
                            break;
                        }
                    }

                    definedFunctions.add(funcName);
                    if (!declared) {
                        Type funcType = new Type(returnType);
                        funcType.isFunction = true;
                        funcType.paramTypes = new ArrayList<>();
                        funcType.paramTypes.add(new Type(Type.Basic.VOID));
                        funcType.returnType = returnType;

                        Symbol funcSymbol = new Symbol(funcName, funcType);
                        globalScope.localVariables.add(funcSymbol);
                        allDefinedFunctions.put(funcName + "_" + funcType.paramTypes.toString(), funcType.paramTypes);
                    }

                    functionStack.push(returnType);

                    newScope();
                    Node slozena = node.children.get(5);
                    slozena.alreadyOpenedScope = true;
                    process(slozena);
                    scopeStack.pop();

                    functionStack.pop();

                } else if (node.children.size() == 6 &&
                        node.children.get(0).label.equals("<ime_tipa>") &&
                        node.children.get(1).label.equals("IDN") &&
                        node.children.get(2).label.equals("L_ZAGRADA") &&
                        node.children.get(3).label.equals("<lista_parametara>") &&
                        node.children.get(4).label.equals("D_ZAGRADA") &&
                        node.children.get(5).label.equals("<slozena_naredba>")) {

                    process(node.children.get(0));

                    if (node.children.get(0).type.isConst) {
                        err(node);
                    }

                    String funcName = node.children.get(1).lexValue;
                    Type returnType = new Type(node.children.get(0).type);

                    if (definedFunctions.contains(funcName)) {
                        err(node);
                    }

                    process(node.children.get(3));
                    List<Type> paramTypes = node.children.get(3).types;
                    List<String> paramNames = node.children.get(3).lexValues; // Need to capture names too

                    scopeNode globalScope = scopeStack.firstElement();
                    boolean declared = false;
                    for (Symbol s : globalScope.localVariables) {
                        if (s.lexValue.equals(funcName)) {
                            declared = true;
                            if (!s.type.isFunction ||
                                    s.type.paramTypes.size() != paramTypes.size() ||
                                    s.type.returnType.basic != returnType.basic) {
                                err(node);
                            }
                            for (int i = 0; i < paramTypes.size(); ++i) {
                                if (s.type.paramTypes.get(i).basic != paramTypes.get(i).basic) {
                                    err(node);
                                }
                            }
                            break;
                        }
                    }

                    definedFunctions.add(funcName);
                    if (!declared) {
                        Type funcType = new Type(returnType);
                        funcType.isFunction = true;
                        funcType.paramTypes = paramTypes;
                        funcType.returnType = returnType;

                        Symbol funcSymbol = new Symbol(funcName, funcType);
                        globalScope.localVariables.add(funcSymbol);
                        allDefinedFunctions.put(funcName + "_" + funcType.paramTypes.toString(), funcType.paramTypes);
                    }

                    functionStack.push(returnType);

                    newScope();
                    scopeNode paramScope = scopeStack.peek();
                    for (int i = 0; i < paramNames.size(); ++i) {
                        Symbol p = new Symbol(paramNames.get(i), paramTypes.get(i));
                        p.lvalue = true; // params are lvalues
                        p.offset = -4 * (paramTypes.size() - i);
                        paramScope.localVariables.add(p);
                    }

                    Node slozena = node.children.get(5);
                    if (slozena.children.size() == 3) {
                         process(slozena.children.get(1));
                    } else if (slozena.children.size() == 4) {
                         process(slozena.children.get(1));
                         process(slozena.children.get(2));
                    }

                    scopeStack.pop();
                    functionStack.pop();
                }
                currentStackOffset = savedOffset;
                System.out.flush();
                System.setOut(mainOut);
                break;

            case "<lista_parametara>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<deklaracija_parametra>")) {
                    process(node.children.get(0));
                    node.types = new ArrayList<>();
                    node.types.add(node.children.get(0).type);
                    node.lexValues = new ArrayList<>();
                    node.lexValues.add(node.children.get(0).lexValue);
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<lista_parametara>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<deklaracija_parametra>")) {
                    process(node.children.get(0));
                    process(node.children.get(2));
                    if (node.children.get(0).lexValues.contains(node.children.get(2).lexValue)) {
                        err(node);
                    }
                    node.types = new ArrayList<>();
                    node.types.addAll(node.children.get(0).types);
                    node.types.add(node.children.get(2).type);
                    node.lexValues = new ArrayList<>();
                    node.lexValues.addAll(node.children.get(0).lexValues);
                    node.lexValues.add(node.children.get(2).lexValue);
                } else {
                    err(node);
                }
                break;

            case "<deklaracija_parametra>":
                if (node.children.size() == 2 && node.children.get(0).label.equals("<ime_tipa>") && node.children.get(1).label.equals("IDN")) {
                    process(node.children.get(0));
                    if (node.children.get(0).type.basic == Type.Basic.VOID) {
                        err(node);
                    }
                    node.type = node.children.get(0).type;
                    node.lexValue = node.children.get(1).lexValue;
                } else if (node.children.size() == 4 && node.children.get(0).label.equals("<ime_tipa>") && node.children.get(1).label.equals("IDN") && node.children.get(2).label.equals("L_UGL_ZAGRADA") && node.children.get(3).label.equals("D_UGL_ZAGRADA")) {
                    process(node.children.get(0));
                    if (node.children.get(0).type.basic == Type.Basic.VOID) {
                        err(node);
                    }
                    Type base = node.children.get(0).type;
                    Type t = new Type(base.basic);
                    t.isSequence = true;
                    node.type = t;
                    node.lexValue = node.children.get(1).lexValue;
                } else {
                    err(node);
                }
                break;

            case "<lista_deklaracija>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<deklaracija>")) {
                    process(node.children.get(0));
                } else if (node.children.size() == 2 && node.children.get(0).label.equals("<lista_deklaracija>") && node.children.get(1).label.equals("<deklaracija>")) {
                    process(node.children.get(0));
                    process(node.children.get(1));
                } else {
                    err(node);
                }
                break;

            case "<deklaracija>":
                if (node.children.size() == 3) {
                    if (node.children.get(0).label.equals("<ime_tipa>") && node.children.get(1).label.equals("<lista_init_deklaratora>") && node.children.get(2).label.equals("TOCKAZAREZ")) {
                        Node imeTipa = node.children.get(0);
                        Node listaInitDek = node.children.get(1);

                        process(imeTipa);

                        listaInitDek.itype = new Type(imeTipa.type);
                        process(listaInitDek);
                        break;
                    } else {
                        err(node);
                    }
                } else {
                    err(node);
                }
                break;

            case "<lista_init_deklaratora>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<init_deklarator>")) {
                    node.children.get(0).itype = node.itype;
                    process(node.children.get(0));
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<lista_init_deklaratora>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<init_deklarator>")) {
                    node.children.get(0).itype = node.itype;
                    process(node.children.get(0));
                    node.children.get(2).itype = node.itype;
                    process(node.children.get(2));
                } else {
                    err(node);
                }
                break;

            case "<init_deklarator>":
                node.children.get(0).itype = new Type(node.itype);
                Node izravni = node.children.get(0);
                process(izravni);

                scopeNode curr = scopeStack.peek();
                Symbol sym = null;
                String name = izravni.children.get(0).lexValue;
                for (Symbol s : curr.localVariables){
                    if (s.lexValue.equals(name)) {
                        sym = s;
                        break;
                    }
                }
                boolean isGlobal = (curr == scopeStack.firstElement());

                if (node.children.size() == 1) {
                    if (izravni.type.isConst) {
                        err(node);
                    }
                    if (!isGlobal) {
                        if (sym != null) {
                            sym.offset = currentStackOffset;
                            currentStackOffset += 4;
                        }
                        System.out.println("    MOV R0, #0");
                        System.out.println("    PUSH {R0}");
                    }
                    break;
                }

                Node init = node.children.get(2);
                int startOffset = currentStackOffset;
                process(init);
                
                Type varType = izravni.type;
                if (varType == null) err(node);

                if (!varType.isSequence) {
                    if (init.type == null) err(node);

                    Type T = new Type(varType.basic);
                    T.isSequence = false;
                    T.isConst = false;

                    if (!canAssign(init.type, T)) err(node);
                } else {
                    if (init.types == null) err(node);
                    if (init.types.size() > varType.elemNr) err(node);

                    Type T = new Type(varType.basic);
                    T.isSequence = false;
                    T.isConst = false;

                    for (Type U : init.types) {
                        if (!canAssign(U, T)) err(node);
                    }
                    
                    int missing = varType.elemNr - init.types.size();
                    for(int i=0; i<missing; ++i) {
                         System.out.println("    MOV R0, #0");
                         System.out.println("    PUSH {R0}");
                         currentStackOffset += 4;
                    }
                }

                if (isGlobal) {
                    int elemCount = varType.isSequence ? varType.elemNr : 1;
                    System.out.println("    LDR R0, =G_" + name);
                    System.out.println("    ADD R0, R0, #" + ((elemCount - 1) * 4));
                    for(int i=0; i<elemCount; ++i) {
                        System.out.println("    POP {R1}");
                        System.out.println("    STR R1, [R0]");
                        System.out.println("    SUB R0, R0, #4");
                        currentStackOffset -= 4;
                    }
                } else {
                    if (sym != null) {
                        sym.offset = startOffset;
                    }
                }
                break;

            case "<izravni_deklarator>":
                if (node.children.size() == 1) {
                    if (node.itype.basic == Type.Basic.VOID) err(node);

                    curr = scopeStack.peek();
                    for (Symbol s : curr.localVariables) {
                        if (s.lexValue.equals(node.children.get(0).lexValue)) {
                            err(node);
                        }
                    }

                    Type t = new Type(node.itype);
                    node.type = t;
                    Symbol s = new Symbol(node.children.get(0).lexValue, t);
                    s.lvalue = !s.type.isConst && !s.type.isSequence;
                    curr.localVariables.add(s);
                    
                    if (curr == scopeStack.firstElement()) {
                        PrintStream old = System.out;
                        System.setOut(funcOut);
                        System.out.println("G_" + s.lexValue + ": .word 0");
                        System.setOut(old);
                    }

                } else if (node.children.size() == 4 && node.children.get(1).label.equals("L_UGL_ZAGRADA")) {
                    if (node.itype.basic == Type.Basic.VOID) err(node);

                    curr = scopeStack.peek();
                    for (Symbol s : curr.localVariables) {
                        if (s.lexValue.equals(node.children.get(0).lexValue)) {
                            err(node);
                        }
                    }

                    long brElem = Long.parseLong(node.children.get(2).lexValue);
                    if (brElem <= 0 || brElem > 1024) err(node);

                    Type t = new Type(node.itype.basic);
                    t.isSequence = true;
                    t.elemNr = (int) brElem;

                    node.type = t;
                    Symbol s = new Symbol(node.children.get(0).lexValue, t);
                    s.lvalue = false;
                    curr.localVariables.add(s);
                    
                    if (curr == scopeStack.firstElement()) {
                        PrintStream old = System.out;
                        System.setOut(funcOut);
                        // Use .word 0 for each element to be safe and compatible
                        System.out.println("G_" + s.lexValue + ":");
                        for(int i=0; i<t.elemNr; ++i) System.out.println("    .word 0");
                        System.setOut(old);
                    }

                } else if (node.children.size() == 4 && node.children.get(1).label.equals("L_ZAGRADA")) {
                    List<Type> paramTypes = new ArrayList<>();
                    if (node.children.get(2).label.equals("<lista_parametara>")) {
                        process(node.children.get(2));
                        paramTypes = new ArrayList<>(node.children.get(2).types);
                    } else {
                        paramTypes.add(new Type(Type.Basic.VOID));
                    }

                    Type targetFuncType = new Type(Type.Basic.VOID);
                    targetFuncType.isFunction = true;
                    targetFuncType.paramTypes = paramTypes;

                    targetFuncType.returnType = new Type(node.itype);

                    curr = scopeStack.peek();
                    Symbol existing = null;
                    for (Symbol s : curr.localVariables) {
                        if (s.lexValue.equals(node.children.get(0).lexValue)) {
                            existing = s;
                            break;
                        }
                    }

                    if (existing != null) {
                        if (!isSameFunction(existing.type, targetFuncType)) {
                            err(node);
                        }
                    } else {
                        curr.localVariables.add(new Symbol(node.children.get(0).lexValue, targetFuncType));
                        allDeclaredFunctions.put(node.children.get(0).lexValue, targetFuncType);
                    }

                    node.type = targetFuncType;
                }
                break;

            case "<inicijalizator>":
                if (node.children.size() == 1) {
                    Node izraz_pri = node.children.get(0);
                    process(izraz_pri);

                    if (izraz_pri.type != null && izraz_pri.type.isSequence &&
                            izraz_pri.type.basic == Type.Basic.CHAR &&
                            izraz_pri.type.isStringLiteral) {

                        node.types = new ArrayList<>();
                        for (int i = 0; i < izraz_pri.type.elemNr; i++) {
                            node.types.add(new Type(Type.Basic.CHAR));
                        }
                    } else {
                        node.type = izraz_pri.type;
                        node.types = null;
                    }
                } else {
                    Node lista = node.children.get(1);
                    process(lista);
                    node.types = new ArrayList<>(lista.types);
                }
                break;

            case "<lista_izraza_pridruzivanja>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<izraz_pridruzivanja>")) {
                    process(node.children.get(0));
                    node.types = new ArrayList<>();
                    node.types.add(node.children.get(0).type);
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<lista_izraza_pridruzivanja>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<izraz_pridruzivanja>")) {
                    process(node.children.get(0));
                    process(node.children.get(2));
                    node.types = new ArrayList<>();
                    node.types.addAll(node.children.get(0).types);
                    node.types.add(node.children.get(2).type);
                } else {
                    err(node);
                }
                break;

            default:
                return;
        }
    }

    static void err(Node node) {
        System.out.print(node.label + " ::=");
        for (Node child : node.children) {
            System.out.print(" ");
            if (child.label.startsWith("<")) {
                System.out.print(child.label);
            } else {
                System.out.print(child.label + "(" + child.row + "," + child.lexValue + ")");
            }
        }
        System.out.println();
        System.exit(0);
    }

    public static void main(String[] args) {
        try {
            mainOut = new PrintStream(new FileOutputStream("a.s"));
            System.setOut(mainOut);
        } catch (IOException e) {
            e.printStackTrace();
            return;
        }

        System.out.println("    LDR SP, =0x20000");
        
        Node root = null;
        try {
            root = loadTree();
        } catch (IOException e) {
            e.printStackTrace();
        }

        // Initialize global scope
        scopeStack.push(new scopeNode(null));

        process(root);
        checkMain();
        
        System.out.println("    BL F_MAIN");
        System.out.println("    SWI 0");
        System.out.print(funcBuffer.toString());

        System.out.println("\nMDIV:");
        System.out.println("    PUSH {R2, R3, R4, R5, LR}");
        System.out.println("    EOR R4, R0, R1");
        System.out.println("    MOV R5, R0");
        System.out.println("    CMP R0, #0");
        System.out.println("    RSBMI R0, R0, #0");
        System.out.println("    CMP R1, #0");
        System.out.println("    RSBMI R1, R1, #0");
        System.out.println("    MOV R2, #0");
        System.out.println("    MOV R3, #0");
        System.out.println("    MOV R12, #32");
        System.out.println("div_loop:");
        System.out.println("    MOV R2, R2, LSL #1");
        System.out.println("    MOV R3, R3, LSL #1");
        System.out.println("    MOVS R0, R0, LSL #1");
        System.out.println("    ADC R3, R3, #0");
        System.out.println("    CMP R3, R1");
        System.out.println("    SUBGE R3, R3, R1");
        System.out.println("    ADDGE R2, R2, #1");
        System.out.println("    SUBS R12, R12, #1");
        System.out.println("    BNE div_loop");
        System.out.println("    MOV R0, R2");
        System.out.println("    MOV R1, R3");
        System.out.println("    CMP R4, #0");
        System.out.println("    RSBMI R0, R0, #0");
        System.out.println("    CMP R5, #0");
        System.out.println("    RSBMI R1, R1, #0");
        System.out.println("    POP {R2, R3, R4, R5, PC}");
        System.out.println("DO_DIV:");
        System.out.println("    PUSH {LR}");
        System.out.println("    BL MDIV");
        System.out.println("    POP {PC}");
        System.out.println("DO_MOD:");
        System.out.println("    PUSH {LR}");
        System.out.println("    BL MDIV");
        System.out.println("    MOV R0, R1");
        System.out.println("    POP {PC}");
        
        mainOut.close();
    }

    static void checkMain() {
        boolean foundReference = false;
        scopeNode global = scopeStack.pop();
        while(!scopeStack.isEmpty())
            global = scopeStack.pop();

        for (Symbol s : global.localVariables) {
            if (s.lexValue.equals("main") && s.type.isFunction &&
                s.type.returnType.basic == Type.Basic.INT &&
                s.type.paramTypes.size() == 1 &&
                s.type.paramTypes.get(0).basic == Type.Basic.VOID) {
                foundReference = true;
                break;
            }
        }

        if (!foundReference || !definedFunctions.contains("main")) {
             System.out.println("main");
             System.exit(0);
        }

        // Check for declared but undefined functions
        for (Symbol s : global.localVariables) {
            if (s.type.isFunction) {
                // If it is declared (in symbol table) but not defined (in definedFunctions set)
                if (!definedFunctions.contains(s.lexValue)) {
                    System.out.println("funkcija");
                    System.exit(0);
                }
            }
        }
        for (String name : allDeclaredFunctions.keySet()) {
            if (!definedFunctions.contains(name)) {
                System.out.println("funkcija");
                System.exit(0);
            }
        }

        for (String name : allDeclaredFunctions.keySet()) {
            if (!allDefinedFunctions.containsKey(name)) {
                System.out.println("funkcija");
                System.exit(0);
            }
        }
    }
}
