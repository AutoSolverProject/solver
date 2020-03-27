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
		if (pair.second > coefficient)
		{
			entering = pair.first;
			coefficient = pair.second;
		}
		else if (pair.second == coefficient)
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
        for (const auto &pair : dictionary.rows[i].variableToCoefficient)
        {
            if (pair.first == entering)
            {
                if (!isZero(pair.second))
                {
                    double curr_ratio = dictionary.rows[i].scalar / -pair.second;
                    if (curr_ratio > 0 && curr_ratio < ratio)
                    {
                        ratio = curr_ratio;
                        leaving = dictionary.rows[i].lhs;
                    }
                    else if (curr_ratio == ratio && dictionary.rows[i].lhs < leaving)
                    {
                        leaving = dictionary.rows[i].lhs;
                    }
                }
            }
        }
	}
    return leaving;
}

void performPivot( Dictionary &dictionary, unsigned entering, unsigned leaving )
{
    // TODO:
    // Perform the pivot operation. You need to:
    //   - Find the row corresponding to the leaving variable
    //   - Perform the pivot operation on that row by isolating the entering variable
    //   - Use the pivot row to eliminate the entering variable from all other equations
    //   - Eliminate the entering variable from the objective function.
	unsigned i;
	for (i = 0; i < m; ++i)
	{
		if (dictionary.rows[i].lhs == leaving) break;
	}
    DictionaryRow pivoting_row = dictionary.rows[i];
    DictionaryRow new_row;
    double entering_coefficient = -pivoting_row.variableToCoefficient[entering];
    new_row.lhs = entering;
    new_row.scalar = pivoting_row.scalar / entering_coefficient;
    for (const auto &pair : pivoting_row.variableToCoefficient)
    {
        if (pair.first == entering) continue;
        new_row.variableToCoefficient[pair.first] = pair.second / entering_coefficient;
    }
    new_row.variableToCoefficient[leaving] = -1 / entering_coefficient;
    dictionary.rows[i] = new_row;
    DictionaryRow curr_row;
    pivoting_row = new_row;
    for (unsigned j = 0; j < m; ++j)
    {
        if (j == i) continue;
        DictionaryRow updated_row;
        curr_row = dictionary.rows[j];
        entering_coefficient = curr_row.variableToCoefficient[entering];
        updated_row.lhs = curr_row.lhs;
        updated_row.scalar = curr_row.scalar + pivoting_row.scalar * entering_coefficient;
        for (const auto &pair : curr_row.variableToCoefficient)
        {
            if (pair.first == entering) continue;
            updated_row.variableToCoefficient[pair.first] =
                    pair.second + pivoting_row.variableToCoefficient[pair.first] *
                                          entering_coefficient;
        }
        updated_row.variableToCoefficient[leaving] = pivoting_row.variableToCoefficient[leaving]
                                                     * entering_coefficient;
        dictionary.rows[j] = updated_row;
    }
    entering_coefficient = dictionary.objectiveCoefficients[entering];
    std::map<unsigned, double> updatedObjectiveCoefficients;
    for (const auto &pair : dictionary.objectiveCoefficients)
    {
        if (pair.first == entering) continue;
        updatedObjectiveCoefficients[pair.first] =
                pair.second + pivoting_row.variableToCoefficient[pair.first] * entering_coefficient;
    }
    updatedObjectiveCoefficients[leaving] =
            entering_coefficient * pivoting_row.variableToCoefficient[leaving];
    dictionary.objectiveScalar += pivoting_row.scalar * entering_coefficient;
    dictionary.objectiveCoefficients = updatedObjectiveCoefficients;
        
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
