function KNN
%Function classifies points as red or blue using the 3-Nearest Neighbor
%algorithm. 

redx = [0 2 4];
redy = [1 3 4];
bluex = [2 5 6];
bluey = [0 2 3];

figure
hold on
title('KNN Test Part C')
xlabel('x')
ylabel('y')

for rx = 1 : length(redx)
    plot(redx(rx),redy(rx), 'ro')
    plot(bluex(rx),bluey(rx), 'bo')
end

for x = 0 : 8
    for y = 0 : 8
        nearcol = [0 0 0]; % 0 represents blue, 1 red check for total
        mindist = [inf inf inf];
        for data = 1 : length(redx)
            reddist = sqrt((x-redx(data))^2 + (y - redy(data))^2);
            bluedist = sqrt((x-bluex(data))^2 + (y - bluey(data))^2);
            if reddist < mindist(1) || equality(reddist, mindist(1))
                nearcol = [1 nearcol(1) nearcol(2)];
                mindist = [reddist mindist(1) mindist(2)];
            elseif reddist < mindist(2) || equality(reddist, mindist(2))
                nearcol = [nearcol(1) 1 nearcol(2)];
                mindist = [mindist(1) reddist mindist(2)];
            elseif reddist < mindist(3) || equality(reddist, mindist(3))
                nearcol = [nearcol(1) nearcol(2) 1];
                mindist = [mindist(1) mindist(2) reddist];
            end
            if bluedist < mindist(1) || equality(bluedist, mindist(1))
                nearcol = [0 nearcol(1) nearcol(2)];
                mindist = [bluedist mindist(1) mindist(2)];
            elseif bluedist < mindist(2) || equality(bluedist, mindist(2))
                nearcol = [nearcol(1) 0 nearcol(2)];
                mindist = [mindist(1) bluedist mindist(2)];
            elseif bluedist < mindist(3) || equality(bluedist, mindist(1))
                nearcol = [nearcol(1) nearcol(2) 0];
                mindist = [mindist(1) mindist(2) bluedist];
            end
        end
        total = sum(nearcol);
        if total >= 2
            col = 'r*';
        else
            col = 'b*';
        end
        plot(x,y,col)
    end
end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

function [tf] = equality(dist1, dist2)
% checks to see if the two numbers are equal
% if the are equal, randomly decides if it should be counted as higher
    if dist1 == dist2
        a = rand;
        if a > .5
            tf = 0;
        else 
            tf = 1;
        end
    else 
        tf = 0;
    end
