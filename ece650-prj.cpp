#include <bits/stdc++.h>
#include "minisat/core/SolverTypes.h"
#include "minisat/core/Solver.h"
#include <thread>
#include <pthread.h>
// C++ library for multithreading
#include <time.h>
#include <iomanip>

#include <chrono>

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

int val,res;
std::vector<int> graphVector;
int bufferX[999], bufferY[999];
bool visitedVertex[999];
bool flag;
std::queue <int> pathQueue;
std::string oprStr,tempString;

std::vector<int> resSAT;
std::vector<int> resVC1;
std::vector<int> resVC2;


// static void *
// thread_start(void *arg)
// {
//     printf("Subthread starting infinite loop\n");
//     for (;;)
//         continue;
// }

// static void
// pclock(char *msg, clockid_t cid)
// {
//     struct timespec ts;

//     printf("%s", msg);
//     if (clock_gettime(cid, &ts) == -1)
//         handle_error("clock_gettime");
//     printf("%4jd.%03ld s\n", (intmax_t) ts.tv_sec, ts.tv_nsec / 1000);
// }



void setVertices(int inpVal)
{
    val=inpVal;
}

void flushValues()
{
    graphVector.clear();
    memset(visitedVertex, false, sizeof(visitedVertex));
    flag = false;

    // graphVector[999] = {0};
}

bool parseString(std::string edgeString) 
{
    int size = edgeString.length();
    int front = 0, rear = 0;
    for(int i = 0;i <= size-1;i++)
    {
        char switchChar = edgeString[i];
        switch(switchChar)
        {
            case '<':
                front = i+1;
                break;
            
            case ',':
                rear = i;
                break;
            
            case '>':
                int x = stoi(edgeString.substr(front, rear-front));
                int y = stoi(edgeString.substr(rear+1, i-rear-1));

                // std::cout<<"-------------------------------------"<<std::endl;

                // std::cout<<"x:: "<<x<<", y:: "<<y<<std::endl;

                // if(x < 1)
                //     std::cout<<"x < 1 False, "<<x<<"<"<<1<<std::endl;
                // if(x > val)
                //     std::cout<<"x > val False, "<<x <<">"<<val<<std::endl;
                // if(y < 1)
                //     std::cout<<"y < 1 False, "<<y <<"<"<<1<<std::endl;
                // if(y > val)
                //     std::cout<<"y > val False, "<<y <<">"<<val<<std::endl;

                // std::cout<<std::endl;
                // std::cout<<std::endl;
                // std::cout<<std::endl;
                
                if(x < 1 || x > val || y < 1 || y > val)
                    return false;
                
                // std::cout<<"added "<<y<<" and "<<x<<std::endl;
                graphVector.push_back(y);
                graphVector.push_back(x);
        }
    }
    return true;
}


static void *doCNF(void *arg) 
{
    // clockid_t cid;
    // int s;

    int t1=0,t2=0,t3=0;
    while (true) 
    {
        Minisat::Solver* solver = new Minisat::Solver();
        std::vector<std::vector<Minisat::Lit>> clausesVector;

        // make literals

        for (t2 = 0; t2 < t1; t2++) 
        {
            std::vector<Minisat::Lit> temp;
            for (t3 = 0; t3 < val; t3++) 
            {
                temp.push_back(Minisat::mkLit(solver->newVar()));
            }
            clausesVector.push_back(temp);
        }

        // At least one vertex is the ith vertex in the vertex cover

        for (auto i = 0; i < t1; i++) 
        {
            Minisat::vec<Minisat::Lit> cl;
            for (auto j = 0; j < val; j++) 
            {
                cl.push(clausesVector[i][j]);
            }
            solver->addClause(cl);
        }

        // add clause for each ij and ik indexes

        for (auto i = 0; i < t1; i++) 
        {
            for (auto j = 0; j < val; j++) 
            {
                for (auto k = j + 1; k < val; k++) 
                {
                    solver->addClause(~clausesVector[i][j], ~clausesVector[i][k]);
                }
            }
        }
        // No one vertex can appear twice in a vertex cover
        for (auto x = 0; x < val; x++) 
        {
            for (auto y = 0; y < t1; y++) 
            {
                for (auto z = y + 1; z < t1; z++) 
                {
                    solver->addClause(~clausesVector[y][x], ~clausesVector[z][x]);
                }
            }
        }

        // Every edge is incident to at least one vertex in the vertex cover

        for (unsigned int i = 0; i < graphVector.size(); i += 2) 
        {
            Minisat::vec<Minisat::Lit> cl;
            for (auto j = 0; j < t1; j++) 
            {
                cl.push(clausesVector[j][graphVector[i + 1]]);
                cl.push(clausesVector[j][graphVector[i]]);
            }
            solver->addClause(cl);
        }


        if (solver->solve()) 
        {
            std::vector<int> vec;
            for (auto i = 0; i < t1; i++) 
            {
                for (auto j = 0; j < val; j++) 
                {
                    if(Minisat::toInt(solver->modelValue(clausesVector[i][j])) == 0)
                        vec.push_back(j);
                }
            }
            // std::cout<<vec.size()<<std::endl;
            sort(vec.begin(), vec.end());
            // std::cout <<"CNF-SAT-VC: ";
            // for (unsigned int t3 = 0; t3 < vec.size(); t3++)
            // {
            //     std::cout << vec[t3];
            //     if(t3!=vec.size()-1)
            //         std::cout <<" ";
            // }
            // std::cout << std::endl;

            resSAT = vec;

            break;
        }
        t1++;
        delete(solver);
    }
    // s = pthread_getcpuclockid(pthread_self(), &cid);
    // // if (s != 0)
    //     //handle_error_en(s, "pthread_getcpuclockid");
    // pclock("CNF-SAT-VC running time", cid);
    // std::cout<< std::endl;
}


static void *doApproxVC1(void *arg)
{
    // clockid_t cid;
    // int s;

    std::vector<int> ans;
    // std::cout<<"Debug:: ";
    // for(auto i : graphVector)
    //     std::cout<<i<<" ";

    // std::cout<<std::endl;

    std::vector<int> tempVec(graphVector.size(),0);
    // int totalEdges=graphVector.size()/2;
    // std::vector<int> storeByDegree(val,0);

    for(unsigned i=0;i<graphVector.size();i++)
    {
        tempVec[i]=graphVector[i];
        // storeByDegree[graphVector[i]]++;
    }
    // int count =0;

    // std::cout<<"After Iteration "<<count++<<std::endl;
    // for(int i=0;i<storeByDegree.size();i++)
    // {
    //     std::cout<<"Vertex "<<i<<" : "<<storeByDegree[i]<<std::endl;
    // }
    // std::cout<<std::endl;

    // int currentMax = 0;

    std::vector<int> buffer = tempVec;
    
    while (buffer.size()) 
    {
        buffer.clear();

        std::vector<int> storeByDegree(val,0);
        for (unsigned i = 0; i < tempVec.size(); i++)
            if (tempVec[i] != -1)
                storeByDegree[tempVec[i]]++;
            
        auto maxIterator = std::max_element(storeByDegree.begin(), storeByDegree.end());
        ans.push_back(std::distance(storeByDegree.begin(), maxIterator));

        for (unsigned i = 0; i < tempVec.size(); i++) 
        {
            if (tempVec[i] == std::distance(storeByDegree.begin(), maxIterator) 
                || tempVec[i + 1] == std::distance(storeByDegree.begin(), maxIterator)) 
            {
                tempVec[i] = -1;
                tempVec[i + 1] = -1;
            }
            else 
            {
                buffer.push_back(tempVec[i]);
                buffer.push_back(tempVec[i + 1]);
            }
            i++;
        }
        tempVec = buffer;

    //     std::cout<<"After Iteration "<<count++<<std::endl;
    //     for(int i=0;i<storeByDegree.size();i++)
    //     {
    //         std::cout<<"Vertex "<<i<<" : "<<storeByDegree[i]<<std::endl;
    //     }
    //     std::cout<<std::endl;
    // }
    }

    // std::cout <<"APPROX-VC-1: ";
    // for (unsigned int t3 = 0; t3 < ans.size(); t3++)
    // {
    //     std::cout << ans[t3];
    //     if(t3!=ans.size()-1)
    //         std::cout <<",";
    // }
    // std::cout << std::endl;

    resVC1 = ans;

//     s = pthread_getcpuclockid(pthread_self(), &cid);
// //  if (s != 0)
// //   	handle_error_en(s, "pthread_getcpuclockid");
//     pclock("VC1 running time", cid);
//     std::cout << std::endl;
}

static void *doApproxVC2(void *arg)
{
    // clockid_t cid;
    // int s;
    int tempVec[graphVector.size()],totalEdges=graphVector.size()/2;
    std::vector<int> ans;

    for(unsigned i=0;i<graphVector.size();i++)
    {
        tempVec[i]=graphVector[i];
    }
    
    while(totalEdges)
    {
        int first,second;
        for(unsigned i=0;i<graphVector.size();i+=2)
        {
            if(tempVec[i]!=-1)
            {
                first=tempVec[i];
                second=tempVec[i+1];
                break;
            }
        }
        
        ans.push_back(first);
        ans.push_back(second);

        for(unsigned j=0;j<graphVector.size();j++)
        {
            if(tempVec[j]==first||tempVec[j]==second)
            {
                tempVec[j]=-1;
                if(j%2)
                {
                    tempVec[j-1]=-1;
                }else
                {
                    tempVec[j+1]=-1;
                }
                totalEdges--;
            }
        }
    }

    // std::cout <<"APPROX-VC-2: ";
    // for (unsigned int t3 = 0; t3 < ans.size(); t3++)
    // {
    //     std::cout << ans[t3];
    //     if(t3!=ans.size()-1)
    //         std::cout <<",";
    // }
    // std::cout << std::endl;

    resVC2 = ans;
    // s = pthread_getcpuclockid(pthread_self(), &cid);
    // //if (s != 0)
    // //	handle_error_en(s, "pthread_getcpuclockid");
    // pclock("VC2 running time", cid);
    // std::cout << std::endl;
}

void output(std::vector<int> ans)
{
    std::sort(ans.begin(),ans.end());
    for (unsigned int t3 = 0; t3 < ans.size(); t3++)
    {
        std::cout << ans[t3];
        if(t3!=ans.size()-1)
            std::cout <<",";
    }
    std::cout << std::endl;
}

static void *takeInput(void *arg)
{
        while(std::cin>>oprStr) 
        {
            // std::cout<<oprStr<<std::endl;
            char firstChar = oprStr[0];
            switch (firstChar)
            {
                case 'V':
                    flushValues();
                    std::cin >> val;

                    // std::cout<<oprStr<<" "<<val<<std::endl;
                    setVertices(++val);
                    break;
                
                case 'E':
                    std::cin >> tempString;

                    // std::cout<<oprStr<<" "<<tempString<<std::endl;
                    if(!parseString(tempString))
                        std::cout << "Error: vertices out of bound" << std::endl;

                    if(graphVector.size()==0)
                    {
                        std::cout<<"CNF-SAT-VC: "<<std::endl;
                        std::cout<<"APPROX-VC-1: "<<std::endl;
                        std::cout<<"APPROX-VC-2: "<<std::endl;
                        break;
                    }
                    

                    int s;

                    pthread_t thread[3];
                    std::chrono::seconds timeoutDuration(120);

                    s = pthread_create(&thread[0], NULL, doCNF, NULL);
                    s = pthread_create(&thread[1], NULL, doApproxVC1, NULL);
                    s = pthread_create(&thread[2], NULL, doApproxVC2, NULL); 
                    bool flag=true;

                    auto startTime = std::chrono::steady_clock::now();

                    while (pthread_tryjoin_np(thread[0], nullptr) != 0) 
                    {
                        auto currentTime = std::chrono::steady_clock::now();
                        auto elapsedTime = std::chrono::duration_cast<std::chrono::seconds>(currentTime - startTime);

                        if (elapsedTime >= timeoutDuration) 
                        {
                            pthread_cancel(thread[0]);
                            flag=false;
                            std::cout<<"CNF-SAT-VC: timeout"<<std::endl;
                            break;
                        }
                        std::this_thread::sleep_for(std::chrono::milliseconds(100));
                    }

                    pthread_join(thread[1],NULL);
                    pthread_join(thread[2],NULL);

                    if(flag)
                    {
                        std::cout<<"CNF-SAT-VC: ";
                        output(resSAT);
                    }
    
                    std::cout<<"APPROX-VC-1: ";
                    output(resVC1); 
                    std::cout<<"APPROX-VC-2: ";
                    output(resVC2); 

                    break;
                
            }
        }
}

int main() 
{
    std::ios_base::sync_with_stdio(false);
    std::cin.tie(NULL);

    pthread_t input;
    int s;
    s = pthread_create(&input, NULL, takeInput, NULL);
    pthread_join(input,NULL);
    // pthread_exit(NULL);
    
    return 0;
}