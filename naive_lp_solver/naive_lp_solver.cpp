#include <cstdio>
#include <fstream>
#include <list>
#include <map>
#include <string.h>
#include <string>
#include <vector>
#include <cfloat>
#include <limits>

const unsigned n = 9;
const unsigned m = 5;

bool isZero( double x )
{
    const double epsilon = 0.0000000001;
    return ( -epsilon <= x ) && ( x <= epsilon );
}

struct DictionaryRow
{
public:
	// A dictionary row describes an equation
	//
	//   lhs = scalar + sum( variable * coefficient )
	//
	
    std::map<unsigned, double> variableToCoefficient;
    double scalar;
    unsigned lhs;
};

struct Dictionary
{
public:
	// A dictionary has an array of rows, and information
	// about the objective function:
	//
	//    z = objectiveScalar + sum( variable * coefficient )
	//

    DictionaryRow rows[m];
    std::map<unsigned, double> objectiveCoefficients;
    double objectiveScalar;
    

    void dump( unsigned iteration ) const
    {
        printf( "\n" );
        printf( "Dumping current dictionary (iteration %u):\n", iteration );
        for ( unsigned i = 0; i < m; ++i )
        {
            printf( "\tx%u = %.2lf ", rows[i].lhs, rows[i].scalar );

            for ( const auto &pair : rows[i].variableToCoefficient )
            {
                unsigned variable = pair.first;
                double coefficient = pair.second;

                if ( isZero( coefficient ) )
                    printf( "          " );
                else if ( coefficient > 0 )
                    printf( "+ %.2lf x%u ", coefficient, variable );
                else
                    printf( "- %.2lf x%u ", -coefficient, variable );
            }
            printf( "\n" );
        }

        printf( "\n\tz  = %.2lf ", objectiveScalar );
        for ( const auto &pair : objectiveCoefficients )
        {
            unsigned variable = pair.first;
            double coefficient = pair.second;
            if ( isZero( coefficient ) )
                printf( "          " );
            else if ( coefficient > 0 )
                printf( "+ %.2lf x%u ", coefficient, variable );
            else
                printf( "- %.2lf x%u ", -coefficient, variable );
        }

        printf( "\n\n" );
    }
};

void readInputProblem( double *A, double *b, double *c )
{
    // The problem is hardcoded

    double constraintMatrix[] = {
        1, 1, 1, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 1, 1, 1, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 1, 1, 1,
        0, 1, 0, 0, 1, 0, 0, 1, 0,
        0, 0, 1, 0, 0, 1, 0, 0, 1,
    };

    double scalars[] = {
        480, 400, 230, 420, 250
    };

    double objective[] = {
        8, 14, 11, 4, 12, 7, 4, 13, 9
    };

    memcpy( A, constraintMatrix, n * m * sizeof(double) );
    memcpy( b, scalars, m * sizeof(double) );
    memcpy( c, objective, n * sizeof(double) );
}

bool optimalSolutionReached( const Dictionary &dictionary )
{
    for (const auto &pair : dictionary.objectiveCoefficients)
	{
		if (pair.second > 0)
		{
			return false;
		}
	}
    return true;
}

unsigned pickEnteringVariable( const Dictionary &dictionary )
{
    unsigned entering = 0;
	double coefficient = 0;
	for (const auto &pair : dictionary.objectiveCoefficients)
	{
		if (pair.second > coefficient)  // use Dantzig's rule to select entering variable
		{
			entering = pair.first;
			coefficient = pair.second;
		}
		else if (pair.second == coefficient)    // use Bland's rule to break ties
		{
			if (pair.first < entering)
			{
				entering = pair.first;
			}
		}
	}
    return entering;
}

unsigned pickLeavingVariable( const Dictionary &dictionary, unsigned entering )
{
    unsigned leaving = 0;
    double ratio = DBL_MAX;     // initialize to a very big number
	for (unsigned i = 0; i < m; ++i)
	{
        for (const auto &pair : dictionary.rows[i].variableToCoefficient)   // find row where entering has the tightest bound
        {
            if (pair.first == entering)
            {
                if (!isZero(pair.second))
                {
                    double currentRatio = dictionary.rows[i].scalar / -pair.second;
                    if (currentRatio > 0 && currentRatio < ratio)
                    {
                        ratio = currentRatio;
                        leaving = dictionary.rows[i].lhs;
                    }
                    else if (currentRatio == ratio && dictionary.rows[i].lhs < leaving)
                    {
                        leaving = dictionary.rows[i].lhs;
                    }
                }
            }
        }
	}
    return leaving;
}

unsigned findPivotingRow( const Dictionary &dictionary, unsigned leaving )
{
    unsigned i;
	for (i = 0; i < m; ++i)
	{
		if (dictionary.rows[i].lhs == leaving) break;
	}
    return i;
}

void pivot( DictionaryRow &pivotingRow, unsigned entering, unsigned leaving )
{
    DictionaryRow pivotedRow;
    double enteringCoefficient = -pivotingRow.variableToCoefficient[entering];
    pivotedRow.lhs = entering;
    pivotedRow.scalar = pivotingRow.scalar / enteringCoefficient;
    for (const auto &pair : pivotingRow.variableToCoefficient)
    {
        if (pair.first == entering) continue;
        pivotedRow.variableToCoefficient[pair.first] = pair.second / enteringCoefficient;
    }
    pivotedRow.variableToCoefficient[leaving] = -1 / enteringCoefficient;
    pivotingRow = pivotedRow;
}

void eliminateEnteringInRows( Dictionary &dictionary, DictionaryRow &pivotingRow, unsigned entering, unsigned leaving, unsigned i )
{
    DictionaryRow currentRow;
    double enteringCoefficient;
    for (unsigned j = 0; j < m; ++j)
    {
        if (j == i) continue;
        DictionaryRow updatedRow;
        currentRow = dictionary.rows[j];
        enteringCoefficient = currentRow.variableToCoefficient[entering];
        updatedRow.lhs = currentRow.lhs;
        updatedRow.scalar = currentRow.scalar + pivotingRow.scalar * enteringCoefficient;
        for (const auto &pair : currentRow.variableToCoefficient)
        {
            if (pair.first == entering) continue;
            updatedRow.variableToCoefficient[pair.first] =
                    pair.second + pivotingRow.variableToCoefficient[pair.first] * enteringCoefficient;
        }
        updatedRow.variableToCoefficient[leaving] = pivotingRow.variableToCoefficient[leaving] * enteringCoefficient;
        dictionary.rows[j] = updatedRow;
    }
}

void eliminateEnteringInObjective( Dictionary &dictionary, DictionaryRow &pivotingRow, unsigned entering, unsigned leaving )
{
    double enteringCoefficient = dictionary.objectiveCoefficients[entering];
    std::map<unsigned, double> updatedObjectiveCoefficients;
    for (const auto &pair : dictionary.objectiveCoefficients)
    {
        if (pair.first == entering) continue;
        updatedObjectiveCoefficients[pair.first] =
                pair.second + pivotingRow.variableToCoefficient[pair.first] * enteringCoefficient;
    }
    updatedObjectiveCoefficients[leaving] =
            enteringCoefficient * pivotingRow.variableToCoefficient[leaving];
    dictionary.objectiveScalar += pivotingRow.scalar * enteringCoefficient;
    dictionary.objectiveCoefficients = updatedObjectiveCoefficients;
}

void performPivot( Dictionary &dictionary, unsigned entering, unsigned leaving )
{
    unsigned i = findPivotingRow( dictionary, leaving );   //   - Find the row corresponding to the leaving variable;
	DictionaryRow pivotingRow = dictionary.rows[i];
    pivot( pivotingRow, entering, leaving );    //   - Perform the pivot operation on that row by isolating the entering variable
    dictionary.rows[i] = pivotingRow;
    eliminateEnteringInRows( dictionary, pivotingRow, entering, leaving, i );    //   - Use the pivot row to eliminate the entering variable from all other equations
    eliminateEnteringInObjective( dictionary, pivotingRow, entering, leaving );     //   - Eliminate the entering variable from the objective function.
}

void prepareInitialDictionary( Dictionary &dictionary, double *A, double *b, double *c )
{
    unsigned rowCounter;

    // Copy from the constraint matrix
    for ( unsigned i = 0; i < m; ++i )
    {
        dictionary.rows[i].lhs = i + n;
        dictionary.rows[i].scalar = b[i];
        for ( unsigned j = 0; j < n; ++j )
            dictionary.rows[i].variableToCoefficient[j] = -A[i*n + j];
    }

    // Zero out the coefficients for the slack variables
    for ( unsigned i = 0; i < m; ++i )
        for ( unsigned j = 0; j < m; ++j )
            dictionary.rows[i].variableToCoefficient[n + j] = 0;

    // Objective function coefficients
    for ( unsigned i = 0; i < n; ++i )
        dictionary.objectiveCoefficients[i] = c[i];
}

int main()
{
    
    /*
      Data structures for the input
    */

    // Constraint matrix:
    double A[n*m];

    // Vector of scalars
    double b[m];

    // Objective function coefficients
    double c[n];

    /*
      Read the input problem
    */
    readInputProblem( A, b, c );

    /*
      Sanity check: ensure all scalars are positive, so the initial
      assignment forms a feasible solution
    */
    for ( unsigned i = 0; i < m; ++i )
    {
        if ( b[i] < 0 )
        {
            printf( "Error! Only non-negative scalars are currently supported.\n" );
            exit( 1 );
        }
    }

    /*
      Prepare the initial dictionary
    */

    Dictionary dictionary;
    prepareInitialDictionary( dictionary, A, b, c );
    dictionary.dump( 0 );

    /*
      Now, perform the main simplex loop
    */
    unsigned iterationCounter = 0;
    while ( !optimalSolutionReached( dictionary ) )
    {
        ++iterationCounter;

        // Pick the entering variable
        unsigned entering = pickEnteringVariable( dictionary );
        printf( "Entering variable: x%u\n", entering );

        // Pick the leaving variable
        unsigned leaving = pickLeavingVariable( dictionary, entering );
        printf( "Leaving variable: x%u\n", leaving );

        // Perform the pivot step
        performPivot( dictionary, entering, leaving );

        dictionary.dump( iterationCounter );
    }

    printf( "\n\nOptimal solution found!\n" );
    printf( "\tMaximal objective value: %.2lf\n", dictionary.objectiveScalar );
    printf( "\tThe optimal solution is: \n" );
    for ( unsigned i = 0; i < n; ++i )
    {
        printf( "\t\tx%u = ", i );
        bool found = false;
        for ( unsigned j = 0; j < m; ++j )
        {
            if ( dictionary.rows[j].lhs == i )
            {
                printf( "%.2lf\n", dictionary.rows[j].scalar );
                found = true;
                break;
            }
        }

        if ( !found )
            printf( "0\n" );
    }

    return 0;
}
